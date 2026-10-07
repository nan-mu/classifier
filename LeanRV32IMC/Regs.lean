import CommonMath
import LeanRV32IMC.Types

namespace LeanRV32IMC
open CommonMath

/-! RV32 register identity mapping onto arch-agnostic `Reg`. -/

def x0Alpha : Nat := 0
def raAlpha : Nat := 1
def spAlpha : Nat := 2
/-- PC uses an alpha outside x0–x31. -/
def pcAlpha : Nat := 32

def regOf (r : regidx) : Reg := Reg.real32 r.toNat

def regX0 : Reg := Reg.real32 x0Alpha
def regRa : Reg := Reg.real32 raAlpha
def regSp : Reg := Reg.real32 spAlpha
def regPc : Reg := Reg.real32 pcAlpha

def isX0 (r : regidx) : Bool := r.toNat == 0

end LeanRV32IMC
