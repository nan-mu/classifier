import CommonMath.Path

namespace EBPF
open CommonMath

/-! External correspondence TBD.
Only logical context and stack inputs are bound: r1=tCtx, r10=tSp.
RV32's tCtx/tSp name the corresponding logical inputs, but its 32-bit wrapper,
context-slot layout, saved registers, and return address are not equated here.
Packet/context loads, resource contracts, helper calls and internal returns are
outside this executable slice. Uninitialized registers have no equality. -/
structure EntryParams where
  tCtx : Term
  tSp : Term

private def leaf64 : Term → Bool
  | .const .w64 c => c < (1 <<< 64)
  | .var .w64 _ => true
  | _ => false

def buildE0 (p : EntryParams) : Except RejectReason SemState := do
  if ![p.tCtx, p.tSp].all leaf64 then throw .invalidEntry
  pure ⟨ExprSet.empty.insertEq (Reg.real64 1) p.tCtx
    |>.insertEq (Reg.real64 10) p.tSp, []⟩

def entrySemState := buildE0

end EBPF
