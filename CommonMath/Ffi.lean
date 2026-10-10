import CommonMath.Numeric
import CommonMath.Virtual
import CommonMath.Render

namespace CommonMath

@[export common_math_add32]
def exportAdd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (ADD .w32 a.toNat b.toNat)

@[export common_math_sub32]
def exportSub32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (SUB .w32 a.toNat b.toNat)

@[export common_math_and32]
def exportAnd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (AND 32 a.toNat b.toNat)

/-- Toward-zero signed quotient bits; div-by-zero and overflow left to callers. -/
@[export common_math_tq32]
def exportTq32 (a b : UInt32) : UInt32 :=
  let x := s 32 a.toNat
  let y := s 32 b.toNat
  if y == 0 then 0xffffffff
  else UInt32.ofNat (M 32 (TQ x y))

@[export common_math_divu32]
def exportDivu32 (a b : UInt32) : UInt32 :=
  let a := a.toNat; let b := b.toNat
  if b == 0 then 0xffffffff
  else UInt32.ofNat (a / b)

private def ffiWidth (bits : UInt32) : Option Width :=
  if bits == 32 then some .w32 else if bits == 64 then some .w64 else none

/-- A binding probe for a resolved canonical cell, without program expansion. -/
@[export lean_virtual_cell_access]
def exportCellAccess (kind width hasOld bitOffset bits sourceWidth isUnsigned write : UInt32)
    (old source : UInt64) : String :=
  let result : Option String := do
    let w ← ffiWidth width
    let v ← ffiWidth sourceWidth
    let k ← if kind == 0 then some RegKind.stack else if kind == 1 then some .map else none
    let reg : Reg := ⟨k, w, 7⟩
    let E := if hasOld == 0 then ExprSet.empty else ExprSet.empty.insertEq reg (Term.C w old.toNat)
    let access : CellAccess := ⟨reg, bitOffset.toNat, bits.toNat⟩
    if write == 0 then
      let t ← access.read E v (isUnsigned != 0)
      some s!"\{\"value\":\"{renderTerm t}\",\"updates\":[]}"
    else
      let updates ← access.write E (Term.C v source.toNat)
      some s!"\{\"updates\":[{renderExprSetJson updates}]}"
  result.getD "null"

/-- A binding probe for byte assembly, including untouched input materialization. -/
@[export lean_virtual_packet_access]
def exportPacketAccess (values : Array UInt32)
    (resource offset bytes width bigEndian isUnsigned allowInput write : UInt32)
    (source : UInt64) : String :=
  let result : Option String := do
    let w ← ffiWidth width
    let E := values.toList.zipIdx.foldl (fun E (value, j) =>
      E.insertEq (Reg.packet resource.toNat j) (Term.C32 (MNat 8 value.toNat))) ExprSet.empty
    let access : PacketAccess := ⟨resource.toNat, offset.toNat, bytes.toNat,
      if bigEndian == 0 then .little else .big,
      if allowInput == 0 then none else some (Term.V64 resource.toNat)⟩
    if write == 0 then
      let read ← access.read E w (isUnsigned != 0)
      some s!"\{\"value\":\"{renderTerm read.value}\",\"inputs\":[{renderExprSetJson read.inputs}]}"
    else
      let updates ← access.write E (Term.C w source.toNat)
      some s!"\{\"updates\":[{renderExprSetJson updates}]}"
  result.getD "null"

end CommonMath
