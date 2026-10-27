import Match.Unify

namespace Match
open Term Term.Value Expression Observation

/-! Local re-pairing inside one node.

`pathMatch` supplies `β_n`. Each index then uses `exprMatch`. A failure inside
a contiguous run of `packetWrite` or `mapWrite` searches a bijection of that
run. The run stops at a helper, branch, return, the other write class, or the
ends of the lists. The original lists are not rewritten. The returned pairs
use the bijection inside the run and `β_n` outside it.

A run longer than six writes is not searched. Independence uses the
observation list only. Targets in the run must be disjoint. A source confirms
a packet read when it is a packet register or `inputByte` at a constant
address. `packetRead` and a symbolic `inputByte` address are not confirmed.
A map run also requires constant map and key terms, and rejects a source that
mentions a map register. An unconfirmed check or a missing bijection is
parameter failure, not a path error. -/

def constNat? : Term → Option Nat
  | .const _ n => some n
  | _ => none

def spansOverlap (a b : Nat × Nat) : Bool :=
  a.1 < b.2 && b.1 < a.2

def pairwiseDisjoint : List (Nat × Nat) → Bool
  | [] => true
  | s :: rest => rest.all (fun t => !spansOverlap s t) && pairwiseDisjoint rest

mutual
  def packetReadSpans : Term → Option (List (Nat × Nat))
    | .const _ _ => some []
    | .var _ _ => some []
    | .regVar _ (.packet b e) => some [(b, e)]
    | .regVar _ _ => some []
    | .app _ (.inputByte _) [_, addr] =>
      match constNat? addr with
      | some a => some [(a * 8, a * 8 + 8)]
      | none => none
    | .app _ (.inputByte _) _ => none
    | .app _ (.packetRead _ _) _ => none
    | .app _ _ args => packetReadSpanList args

  def packetReadSpanList : List Term → Option (List (Nat × Nat))
    | [] => some []
    | t :: ts => do
      let here ← packetReadSpans t
      let rest ← packetReadSpanList ts
      pure (here ++ rest)
end

mutual
  def mentionsMapReg : Term → Bool
    | .regVar _ (.map ..) => true
    | .app _ _ args => mentionsMapList args
    | _ => false

  def mentionsMapList : List Term → Bool
    | [] => false
    | t :: ts => mentionsMapReg t || mentionsMapList ts
end

def zipIndex {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | x :: xs, i => (i, x) :: zipIndex xs (i + 1)

def packetSpan : Observation → Option (Nat × Nat)
  | .packetWrite offset bits _ => some (offset * 8, offset * 8 + bits)
  | _ => none

def readsAvoid (spans reads : List (Nat × Nat)) (self : Nat) : Bool :=
  (zipIndex spans 0).all fun (k, span) =>
    k == self || reads.all fun r => !spansOverlap r span

def observationsAt (xs : List Observation) (ix : List Nat) : Option (List Observation) :=
  ix.mapM fun i => xs[i]?

def packetGroupOk (xs : List Observation) (ix : List Nat) : Bool :=
  match observationsAt xs ix with
  | none => false
  | some obs =>
    match obs.mapM packetSpan with
    | none => false
    | some spans =>
      pairwiseDisjoint spans &&
        (zipIndex obs 0).all fun (k, o) =>
          match o with
          | .packetWrite _ _ source =>
            match packetReadSpans source with
            | some reads => readsAvoid spans reads k
            | none => false
          | _ => false

def mapTarget : Observation → Option (Term × List Term × (Nat × Nat))
  | .mapWrite map key offset bits _ =>
    let map := solve map
    let key := key.map solve
    if (constNat? map).isSome && key.all (fun t => (constNat? t).isSome) then
      some (map, key, (offset * 8, offset * 8 + bits))
    else none
  | _ => none

def mapConflict
    (a b : Term × List Term × (Nat × Nat)) : Bool :=
  a.1 == b.1 && a.2.1 == b.2.1 && spansOverlap a.2.2 b.2.2

def pairwiseMapDisjoint : List (Term × List Term × (Nat × Nat)) → Bool
  | [] => true
  | row :: rest => rest.all (fun other => !mapConflict row other) && pairwiseMapDisjoint rest

def mapGroupOk (xs : List Observation) (ix : List Nat) : Bool :=
  match observationsAt xs ix with
  | none => false
  | some obs =>
    match obs.mapM mapTarget with
    | none => false
    | some rows =>
      pairwiseMapDisjoint rows &&
        obs.all fun o =>
          match o with
          | .mapWrite _ _ _ _ source =>
            !mentionsMapReg source && (packetReadSpans source).isSome
          | _ => false

def groupIndependent (L R : List Observation) (ix : List Nat) : Bool :=
  match ix.head? with
  | some i =>
    match L[i]? with
    | some (.packetWrite ..) => packetGroupOk L ix && packetGroupOk R ix
    | some (.mapWrite ..) => mapGroupOk L ix && mapGroupOk R ix
    | _ => false
  | none => false

def exprsMatch (L R : List Observation) (pairs : List (Nat × Nat)) : Bool :=
  pairs.all fun (i, j) =>
    match L[i]?, R[j]? with
    | some a, some b => (exprMatch a b).isSome
    | _, _ => false

def insertAt : Nat → Nat → List Nat → List Nat
  | 0, x, xs => x :: xs
  | _ + 1, x, [] => [x]
  | n + 1, x, y :: ys => y :: insertAt n x ys

def permutations : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs =>
    let rest := permutations xs
    (List.range (xs.length + 1)).flatMap fun n =>
      rest.map (insertAt n x)
  termination_by xs => xs.length

/-- At most six writes. `none` means the bijection or the independence check
was not confirmed. -/
def findBijection (L R : List Observation) (ix : List Nat) : Option (List (Nat × Nat)) :=
  if ix.length > 6 then none
  else if !groupIndependent L R ix then none
  else
    (permutations ix).findSome? fun perm =>
      let pairs := ix.zip perm
      if exprsMatch L R pairs then some pairs else none

def runStart (L : List Observation) (i : Nat) : Nat :=
  match i with
  | 0 => 0
  | j + 1 =>
    match L[j]?, L[i]? with
    | some prev, some here =>
      if category prev == category here &&
          (category here == "packetWrite" || category here == "mapWrite") then
        runStart L j
      else i
    | _, _ => i
  termination_by i

def runEnd (L : List Observation) (i : Nat) : Nat :=
  let rec go (fuel j : Nat) : Nat :=
    match fuel with
    | 0 => j
    | fuel + 1 =>
      match L[j]?, L[j + 1]? with
      | some here, some next =>
        if category here == category next &&
            (category here == "packetWrite" || category here == "mapWrite") then
          go fuel (j + 1)
        else j
      | _, _ => j
  go L.length i

def indexRun (start finish : Nat) : List Nat :=
  (List.range (finish + 1 - start)).map (· + start)

def dedup (xs : List Nat) : List Nat :=
  xs.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []

def writeRuns (L : List Observation) (failed : List Nat) : List (List Nat) :=
  let starts := dedup (failed.filterMap fun i =>
    match L[i]? with
    | some o =>
      if category o == "packetWrite" || category o == "mapWrite" then
        some (runStart L i)
      else none
    | none => none)
  starts.map fun s => indexRun s (runEnd L s)

def covered (groups : List (List Nat)) (i : Nat) : Bool :=
  groups.any fun g => g.contains i

inductive LocalResult where
  | strict (pairs : List (Nat × Nat))
  | parameter
  | pathError
  deriving Repr

def sortPairs (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  ps.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

def localMatch (L R : List Observation) : LocalResult :=
  match pathMatch L R with
  | none => .pathError
  | some _ =>
    let failed := (List.range L.length).filter fun i =>
      match L[i]?, R[i]? with
      | some a, some b => (exprMatch a b).isNone
      | _, _ => true
    if failed.isEmpty then .strict (identityPairs L.length)
    else
      let groups := writeRuns L failed
      if failed.any fun i => !covered groups i then .parameter
      else
        match groups.mapM (findBijection L R) with
        | none => .parameter
        | some grouped =>
          let inside := groups.flatten
          let outside := (List.range L.length).filter fun i => !inside.contains i
          .strict (sortPairs (outside.map (fun i => (i, i)) ++ grouped.flatten))

def renderLocal : LocalResult → String
  | .strict pairs => s!"\{\"status\":\"ok\",\"pass\":true,\"pairs\":{renderPairs pairs}}"
  | .parameter => "{\"status\":\"ok\",\"pass\":false,\"reason\":\"Parameter\"}"
  | .pathError => "{\"status\":\"fail\",\"reason\":\"PathReject\"}"

@[export lean_match_local]
def exportMatchLocal (leftJson rightJson : String) : String :=
  match parseObservationList leftJson, parseObservationList rightJson with
  | some L, some R => renderLocal (localMatch L R)
  | _, _ => reject

private def pw (offset : Nat) (source : String) : String :=
  s!"\{\"kind\":\"packetWrite\",\"offset\":{offset},\"width\":16,\"source\":\"{source}\"}"

private def arr (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

#guard exportMatchLocal
    (arr [pw 0 "1", pw 2 "1", pw 4 "1", pw 6 "1", pw 8 "1", pw 10 "1"])
    (arr [pw 0 "1", pw 8 "1", pw 2 "1", pw 10 "1", pw 6 "1", pw 4 "1"]) ==
  "{\"status\":\"ok\",\"pass\":true,\"pairs\":[{\"left\":0,\"right\":0},{\"left\":1,\"right\":2},{\"left\":2,\"right\":5},{\"left\":3,\"right\":4},{\"left\":4,\"right\":1},{\"left\":5,\"right\":3}]}"

#guard exportMatchLocal
    (arr [pw 0 "1", pw 0 "2"])
    (arr [pw 0 "2", pw 0 "1"]) ==
  "{\"status\":\"ok\",\"pass\":false,\"reason\":\"Parameter\"}"

#guard exportMatchLocal
    "[{\"kind\":\"branch\",\"position\":1,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"1\",\"rel\":\"eq\",\"rhs\":\"129\"}}]"
    "[{\"kind\":\"branch\",\"position\":1,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"1\",\"rel\":\"eq\",\"rhs\":\"43144\"}}]" ==
  "{\"status\":\"ok\",\"pass\":false,\"reason\":\"Parameter\"}"

#guard exportMatchLocal
    "[{\"kind\":\"ret\",\"width\":32,\"term\":\"1\"}]"
    "[{\"kind\":\"helper\",\"helperId\":1,\"args\":[\"1\"]}]" ==
  "{\"status\":\"fail\",\"reason\":\"PathReject\"}"

end Match
