import CommonMath.Bits
import CommonMath.Op

namespace CommonMath

inductive Term where
  | const (w : Width) (c : Nat)
  | var (w : Width) (ξ : Nat)
  | app (w : Width) (op : Op) (args : List Term)
  deriving Repr, Inhabited

def Term.width : Term → Width
  | .const w _ => w
  | .var w _ => w
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
  deriving DecidableEq, BEq, Repr

def FV : Term → List Var
  | .const _ _ => []
  | .var w ξ => [⟨w, ξ⟩]
  | .app _ _ args => args.foldl (fun acc t => acc ++ FV t) []

def FV.isEmpty (t : Term) : Bool := (FV t).isEmpty

partial def eval : Term → Option Nat
  | .const _ c => some c
  | .var _ _ => none
  | .app _ op args =>
      let rec go : List Term → Option (List Nat)
        | [] => some []
        | t :: ts =>
          match eval t, go ts with
          | some v, some vs => some (v :: vs)
          | _, _ => none
      match go args with
      | some vs => interpretOp op vs
      | none => none

/-- \(\operatorname{solve}_w\): fold closed terms to constants; leave open terms intact. -/
def solve (t : Term) : Term :=
  if FV.isEmpty t then
    match eval t with
    | some c => .const t.width (MNat t.width.bits c)
    | none => t
  else t

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
