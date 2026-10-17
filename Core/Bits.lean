namespace Core

/-- Register / term width set \(W=\{32,64\}\). -/
inductive Width where
  | w32
  | w64
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def Width.bits : Width → Nat
  | .w32 => 32
  | .w64 => 64

def Width.mask (w : Width) : Nat := (1 <<< w.bits) - 1

/-- Instruction encoding widths \(W_{\mathrm{Insn}}=\{16,32,64\}\). -/
inductive InsnWidth where
  | w16 | w32 | w64
  deriving DecidableEq, BEq, Repr, Inhabited

def InsnWidth.bits : InsnWidth → Nat
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

/-- \(M_q(z)=z\bmod 2^q\) with non-negative representative. -/
def M (q : Nat) (z : Int) : Nat :=
  let m := (1 : Int) <<< q
  let r := z % m
  if r < 0 then (r + m).toNat else r.toNat

def MNat (q : Nat) (a : Nat) : Nat := a % (1 <<< q)

def u (q : Nat) (a : Nat) : Nat := MNat q a

def s (q : Nat) (a : Nat) : Int :=
  let a' := MNat q a
  let half := (1 : Nat) <<< (q - 1)
  if a' < half then Int.ofNat a' else Int.ofNat a' - Int.ofNat (1 <<< q)

def indicator (φ : Bool) : Nat := if φ then 1 else 0

def bit (a j : Nat) : Nat := (a / (1 <<< j)) % 2

end Core
