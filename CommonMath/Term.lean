import CommonMath.Bits
import CommonMath.Op
import CommonMath.Reg

namespace CommonMath

inductive Term where
  | const (w : Width) (c : Nat)
  | var (w : Width) (ξ : Nat)
  /-- Value of a register at a fixed dynamic event, rather than a live register lookup. -/
  | regVar (event : Nat) (reg : Reg)
  | app (w : Width) (op : Op) (args : List Term)
  deriving BEq, Repr, Inhabited


def Term.width : Term → Width
  | .const w _ => w
  | .var w _ => w
  | .regVar _ r => r.width
  | .app w _ _ => w

def Term.C (w : Width) (c : Nat) : Term := .const w (MNat w.bits c)
def Term.C32 (c : Nat) : Term := .C .w32 c
def Term.C64 (c : Nat) : Term := .C .w64 c
def Term.V (w : Width) (ξ : Nat) : Term := .var w ξ
def Term.V32 (ξ : Nat) : Term := .V .w32 ξ
def Term.V64 (ξ : Nat) : Term := .V .w64 ξ

structure Var where
  width : Width
  name  : Nat
  register : Option (Nat × Reg) := none
  deriving DecidableEq, BEq, Repr

def FV : Term → List Var
  | .const _ _ => []
  | .var w ξ => [⟨w, ξ, none⟩]
  | .regVar event r => [⟨r.width, r.alpha, some (event, r)⟩]
  | .app _ _ args => args.foldl (fun acc t => acc ++ FV t) []

def FV.isEmpty (t : Term) : Bool := (FV t).isEmpty

mutual
  def eval : Term → Option Nat
    | .const _ c => some c
    | .var _ _ => none
    | .regVar _ _ => none
    | .app _ op args =>
        match evalArgs args with
        | some vs => interpretOp op vs
        | none => none
  termination_by t => sizeOf t

  private def evalArgs : List Term → Option (List Nat)
    | [] => some []
    | t :: ts =>
        match eval t, evalArgs ts with
        | some v, some vs => some (v :: vs)
        | _, _ => none
  termination_by ts => sizeOf ts
end

/-- \(\operatorname{solve}_w\): fold closed terms to constants; leave open terms intact. -/
def solve (t : Term) : Term :=
  if FV.isEmpty t then
    match eval t with
    | some c => .const t.width (MNat t.width.bits c)
    | none => t
  else t

/-- Solving twice has the same result as solving once (§10.1). -/
theorem solve_idempotent (t : Term) : solve (solve t) = solve t := by
  unfold solve
  split
  · split
    · simp [FV.isEmpty, FV, eval, Term.width, MNat]
    · simp_all
  · rfl

/-- \(f^\star(t_1,\ldots,t_n)=\operatorname{solve}_w(f(t_1,\ldots,t_n))\). -/
def star (w : Width) (op : Op) (args : List Term) : Term :=
  solve (.app w op args)

def addStar (w : Width) (t1 t2 : Term) : Term := star w (Op.add w) [t1, t2]
def subStar (w : Width) (t1 t2 : Term) : Term := star w (Op.sub w) [t1, t2]
def mulloStar (w : Width) (t1 t2 : Term) : Term := star w (Op.mullo w) [t1, t2]
def andStar (q : Nat) (w : Width) (t1 t2 : Term) : Term := star w (Op.and q) [t1, t2]
def orStar (q : Nat) (w : Width) (t1 t2 : Term) : Term := star w (Op.or q) [t1, t2]
def xorStar (q : Nat) (w : Width) (t1 t2 : Term) : Term := star w (Op.xor q) [t1, t2]
def shlStar (w : Width) (t1 t2 : Term) : Term := star w (Op.shl w) [t1, t2]
def lshrStar (w : Width) (t1 t2 : Term) : Term := star w (Op.lshr w) [t1, t2]
def ashrStar (w : Width) (t1 t2 : Term) : Term := star w (Op.ashr w) [t1, t2]
def ltuStar (w : Width) (t1 t2 : Term) : Term := star w (Op.ltu w) [t1, t2]
def ltsStar (w : Width) (t1 t2 : Term) : Term := star w (Op.lts w) [t1, t2]
def idStar (w : Width) (t : Term) : Term := star w (Op.id w) [t]
def negStar (w : Width) (t : Term) : Term := star w (Op.neg w) [t]
def zStar (q : Nat) (w : Width) (v : Nat) (t : Term) : Term := star w (Op.zext q w v) [t]
def sStar (q : Nat) (w : Width) (v : Nat) (t : Term) : Term := star w (Op.sext q w v) [t]

end CommonMath
