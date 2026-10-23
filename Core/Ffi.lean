import Core.Numeric
import Core.Virtual
import Core.Render

namespace Core

@[export classifier_expr_add32]
def exportAdd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (ADD .w32 a.toNat b.toNat)

@[export classifier_expr_sub32]
def exportSub32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (SUB .w32 a.toNat b.toNat)

@[export classifier_expr_and32]
def exportAnd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (AND 32 a.toNat b.toNat)

/-- Toward-zero signed quotient bits; div-by-zero and overflow left to callers. -/
@[export classifier_expr_tq32]
def exportTq32 (a b : UInt32) : UInt32 :=
  let x := s 32 a.toNat
  let y := s 32 b.toNat
  if y == 0 then 0xffffffff
  else UInt32.ofNat (M 32 (TQ x y))

@[export classifier_expr_divu32]
def exportDivu32 (a b : UInt32) : UInt32 :=
  let a := a.toNat; let b := b.toNat
  if b == 0 then 0xffffffff
  else UInt32.ofNat (a / b)

private def ffiWidth (bits : UInt32) : Option Width :=
  if bits == 32 then some .w32 else if bits == 64 then some .w64 else none

/-- A binding probe for one stack or map interval, without program expansion. -/
@[export lean_virtual_cell_access]
def exportCellAccess (kind width hasOld bitOffset bits sourceWidth isUnsigned write : UInt32)
    (old source : UInt64) : String :=
  let result : Option String := do
    let w ← ffiWidth width
    let v ← ffiWidth sourceWidth
    if bits == 0 || bitOffset.toNat + bits.toNat > w.bits then none
    let full ← match kind with
      | 0 => some (Reg.stack 0 w.bits)
      | 1 => some (Reg.map 7 [] 0 w.bits)
      | _ => none
    let reg ← match kind with
      | 0 => some (Reg.stack bitOffset.toNat (bitOffset.toNat + bits.toNat))
      | 1 => some (Reg.map 7 [] bitOffset.toNat (bitOffset.toNat + bits.toNat))
      | _ => none
    if !full.valid || !reg.valid then none
    let E ← if hasOld == 0 then some Expr.nil else
      writeInterval Expr.nil full (Term.C w old.toNat)
    let access : CellAccess := ⟨reg⟩
    if write == 0 then
      let t ← access.read E v (isUnsigned != 0)
      some s!"\{\"value\":\"{renderTerm t}\",\"updates\":[]}"
    else
      let updates ← access.write E (Term.C v source.toNat)
      some s!"\{\"updates\":[{renderExprsJson updates}]}"
  result.getD "null"

/-- A binding probe for one packet's byte intervals. -/
@[export lean_virtual_packet_access]
def exportPacketAccess (values : Array UInt32)
    (κ offset bytes width bigEndian isUnsigned allowInput write : UInt32)
    (source : UInt64) : String :=
  let result : Option String := do
    let w ← ffiWidth width
    let mut E := Expr.nil
    for (value, j) in values.toList.zipIdx do
      E ← writeInterval E (.packet (8 * j) (8 * j + 8)) (Term.C32 (value.toNat &&& 255))
    let access : PacketAccess := {
      displacement := .c offset.toNat
      bytes := bytes.toNat
      order := if bigEndian == 0 then .little else .big
      inputBase := if allowInput == 0 then none else some (Term.V64 κ.toNat)
    }
    if write == 0 then
      let read ← access.read E w (isUnsigned != 0)
      some s!"\{\"value\":\"{renderTerm read.value}\",\"inputs\":[{renderExprsJson read.inputs}]}"
    else
      let updates ← access.write E (Term.C w source.toNat)
      some s!"\{\"updates\":[{renderExprsJson updates}]}"
  result.getD "null"

end Core
