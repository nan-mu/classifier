import Match.Prepare

namespace Match
open Term Term.Value Expression Observation Wire

/-! Spellings that denote one comparison.

RV32 writes the packet end as `add32(v32:4,v32:5)`. eBPF writes it as
`add32(v32:4,128)` and carries that 32-bit sum through `zext`, `low`, and
`id`. A branch that mentions either spelling uses one marker for the end.
Address sums are then read at 32 bits with no carry out of bit 31.

Elsewhere a cast is removed only when it leaves the value unchanged: a full
`low` or `extract`, or a `zext` whose argument already fits in the bits it
keeps. `add` and `mullo` narrow to 32 bits only when the mathematical result
is below `2^32`. An `or` of payload bytes is associative and commutative, so
it is flattened and sorted. An `or` that mentions any variable other than the
packet base `v32:4` keeps its shape.

A `*N32` relation compares values modulo `2^32`, so its constants are reduced
and the relation is read in its 32-bit form.

`externalResult`'s event is the expand node that produced the call. It is not
part of the return value. When every argument fits in 32 bits the return is
read at 32 bits: the 64-bit helper register holds that 32-bit result with its
high half clear, so a comparison with zero agrees. -/

def packetEndMarker : Term := Term.V32 900

private def isBase (t : Term) : Bool := t == Term.V32 4

private def isLen (t : Term) : Bool :=
  t == Term.V32 5 || match t with
    | .const _ 128 => true
    | _ => false

private def isPacketEnd : Term → Bool
  | .app _ (.add _) [a, b] => (isBase a && isLen b) || (isBase b && isLen a)
  | _ => false

/-- Bits known to be enough for `t`. A plain variable has no such bound. -/
private def tightBound : Term → Option Nat
  | .const _ c => some (bitLen c)
  | .app _ (.id _) [a] => tightBound a
  | .app _ (.low q _) [_] => some q
  | .app _ (.extract 0 n _) [_] => some n
  | .app _ (.zext q _ _) [a] =>
    match tightBound a with
    | some b => some (min q b)
    | none => some q
  | .app _ (.inputByte _) _ => some 8
  | .app _ (.mullo _) [a, .const _ c] | .app _ (.mullo _) [.const _ c, a] =>
    match tightBound a, natPow2Shift? c with
    | some b, some k => some (b + k)
    | _, _ => none
  | .app _ (.or _) [a, b] =>
    match tightBound a, tightBound b with
    | some x, some y => some (max x y)
    | _, _ => none
  | .app _ (.add _) [a, b] =>
    match tightBound a, tightBound b with
    | some x, some y =>
      if x ≤ 32 && y ≤ 32 && 2 ^ x + 2 ^ y ≤ 2 ^ 32 then some (max x y + 1) else none
    | _, _ => none
  | _ => none
termination_by t => sizeOf t

private def within (q : Nat) (t : Term) : Bool :=
  t.width.bits ≤ q ||
    match tightBound t with
    | some b => b ≤ q
    | none => false

mutual
  private def blocksOr : Term → Bool
    | .var .w32 4 => false
    | .var _ _ => true
    | .regVar _ _ => true
    | .app _ _ args => blocksOrList args
    | _ => false
  termination_by t => sizeOf t

  private def blocksOrList : List Term → Bool
    | [] => false
    | t :: ts => blocksOr t || blocksOrList ts
  termination_by ts => sizeOf ts
end

private def orLeaves : Term → List Term
  | .app _ (.or _) [a, b] => orLeaves a ++ orLeaves b
  | t => [t]
termination_by t => sizeOf t

private def insertRender (x : Term) : List Term → List Term
  | [] => [x]
  | y :: ys =>
    if renderTerm x ≤ renderTerm y then x :: y :: ys else y :: insertRender x ys
termination_by ys => ys.length

private def sortRender : List Term → List Term
  | [] => []
  | x :: xs => insertRender x (sortRender xs)
termination_by xs => xs.length

private def orTree : List Term → Term
  | [] => Term.C32 0
  | [t] => t
  | t :: ts => .app .w32 (.or 32) [t, orTree ts]
termination_by ts => ts.length

private def shrink (t : Term) : Term :=
  match t with
  | .const _ c => if c < 2 ^ 32 then Term.C32 c else t
  | _ => t

mutual
  private def canon : Term → Term
    | .const w c => if c < 2 ^ 32 then Term.C32 c else .const w c
    | .app _ (.id _) [a] => canon a
    | .app w (.low q v) [a] =>
      let a := canon a
      if q == v || within q a then a else .app w (.low q v) [a]
    | .app w (.extract o n v) [a] =>
      let a := canon a
      if o == 0 && (n == v || within n a) then a else .app w (.extract o n v) [a]
    | .app w (.zext q out v) [a] =>
      let a := canon a
      if within q a then a else .app w (.zext q out v) [a]
    | .app w (.externalResult _ lane) args =>
      let args := canonArgs args
      if args.all fun a => a.width == .w32 then
        .app .w32 (.externalResult 0 lane) args
      else
        .app w (.externalResult 0 lane) args
    | .app w (.add ow) [a, b] =>
      let a := canon a
      let b := canon b
      let t := .app w (.add ow) [a, b]
      if isPacketEnd t then packetEndMarker
      else
        match tightBound t with
        | some k => if k ≤ 32 then .app .w32 (.add .w32) [shrink a, shrink b] else t
        | none => t
    | .app w (.mullo ow) [a, b] =>
      let a := canon a
      let b := canon b
      let t := .app w (.mullo ow) [a, b]
      match tightBound t with
      | some k => if k ≤ 32 then .app .w32 (.mullo .w32) [shrink a, shrink b] else t
      | none => t
    | .app w (.or q) [a, b] =>
      let t := .app w (.or q) [canon a, canon b]
      let leaves := orLeaves t
      if leaves.any blocksOr then t
      else if leaves.all (within 32) then orTree (sortRender leaves)
      else t
    | .app w op args => .app w op (canonArgs args)
    | t => t
  termination_by t => sizeOf t

  private def canonArgs : List Term → List Term
    | [] => []
    | a :: as => canon a :: canonArgs as
  termination_by as => sizeOf as
end

mutual
  private def containsMarker : Term → Bool
    | .var _ n => n == 900
    | .app _ _ args => markerIn args
    | _ => false
  termination_by t => sizeOf t

  private def markerIn : List Term → Bool
    | [] => false
    | t :: ts => containsMarker t || markerIn ts
  termination_by ts => sizeOf ts
end

private def fits32 : Term → Bool
  | .const _ c => c < 2 ^ 32
  | .var .w32 _ => true
  | .app .w32 _ _ => true
  | _ => false

mutual
  private def narrow : Term → Term
    | .app w (.add ow) [a, b] =>
      let a := narrow a
      let b := narrow b
      if fits32 a && fits32 b then .app .w32 (.add .w32) [shrink a, shrink b]
      else .app w (.add ow) [a, b]
    | .app w (.sub ow) [a, b] =>
      let a := narrow a
      let b := narrow b
      if fits32 a && fits32 b then .app .w32 (.sub .w32) [shrink a, shrink b]
      else .app w (.sub ow) [a, b]
    | .const _ c => if c < 2 ^ 32 then Term.C32 c else .const .w64 c
    | .app w op args => .app w op (narrowArgs args)
    | t => t
  termination_by t => sizeOf t

  private def narrowArgs : List Term → List Term
    | [] => []
    | a :: as => narrow a :: narrowArgs as
  termination_by as => sizeOf as
end

/-- `leuN32` is the 32-bit compare. Other narrowed relations stay. -/
private def drop32 : Rel → Rel
  | .eqN 32 => .eq
  | .neN 32 => .ne
  | .ltuN 32 => .ltu
  | .leuN 32 => .leu
  | .gtuN 32 => .gtu
  | .geuN 32 => .geu
  | .ltsN 32 => .lts
  | .lesN 32 => .les
  | .gtsN 32 => .gts
  | .gesN 32 => .ges
  | r => r

private def isN32 : Rel → Bool
  | .eqN 32 | .neN 32 | .ltuN 32 | .leuN 32 | .gtuN 32 | .geuN 32
  | .ltsN 32 | .lesN 32 | .gtsN 32 | .gesN 32 => true
  | _ => false

mutual
  private def mod32 : Term → Term
    | .const _ c => Term.C32 (c % (2 ^ 32))
    | .app w op args => .app w op (mod32Args args)
    | t => t
  termination_by t => sizeOf t

  private def mod32Args : List Term → List Term
    | [] => []
    | a :: as => mod32 a :: mod32Args as
  termination_by as => sizeOf as
end

/-- Identify packet-end spellings, 32-bit payload arithmetic, and helper
returns on one prepared observation. -/
def align : Observation → Observation
  | .branch position dir cond =>
    let lhs := canon cond.lhs
    let rhs := canon cond.rhs
    -- A truncating `zext` around an address add becomes the identity only
    -- after that add has been read at 32 bits.
    let marked := containsMarker lhs || containsMarker rhs
    let lhs := if marked then canon (narrow lhs) else lhs
    let rhs := if marked then canon (narrow rhs) else rhs
    let lhs := if isN32 cond.rel then mod32 lhs else lhs
    let rhs := if isN32 cond.rel then mod32 rhs else rhs
    .branch position dir (orderCond { lhs, rel := drop32 cond.rel, rhs })
  | observation => observation

end Match
