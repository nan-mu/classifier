import Core.Term

namespace Core

/-
Virtual memory is a table of disjoint byte-aligned slices.
Each slice is a constant or a projection of one immutable machine term.
A write replaces the bits in its interval and leaves every other bit on its old slice.
-/

inductive MemError where
  | badWidth
  | badAlign
  | badConst
  | empty
  | gap (bit : Nat)
  | overlap (bit : Nat)
  deriving DecidableEq, BEq, Repr

inductive Slice where
  | const (width value : Nat)
  | proj (width : Nat) (source : Term) (shift : Nat)
  deriving DecidableEq, BEq, Repr

def Slice.width : Slice → Nat
  | .const width _ => width
  | .proj width _ _ => width

def Slice.ok : Slice → Bool
  | .const width value =>
      decide (width > 0 ∧ width % 8 = 0 ∧ value < 2 ^ width)
  | .proj width source shift =>
      decide (width > 0 ∧ width % 8 = 0 ∧ shift % 8 = 0 ∧
        shift + width ≤ source.width.bits)

def Slice.error (s : Slice) : MemError :=
  match s with
  | .const width _ => if decide (width = 0 ∨ width % 8 ≠ 0) then .badWidth else .badConst
  | .proj width _ shift =>
      if decide (width = 0 ∨ width % 8 ≠ 0) then .badWidth
      else if decide (shift % 8 ≠ 0) then .badAlign
      else .badWidth

def subslice (s : Slice) (rel width : Nat) : Except MemError Slice := do
  if !(decide (width > 0 ∧ rel + width ≤ s.width)) then throw .badWidth
  let out := match s with
    | .const _ value =>
        Slice.const width ((value >>> rel) &&& ((1 <<< width) - 1))
    | .proj _ source shift =>
        Slice.proj width source (shift + rel)
  if out.ok then pure out else throw out.error

def mergeSlice (a b : Slice) : Option Slice :=
  match a, b with
  | .const width value, .const width' value' =>
      let out := Slice.const (width + width') (value + (value' <<< width))
      if out.ok then some out else none
  | .proj width source shift, .proj width' source' shift' =>
      if source == source' && shift + width == shift' then
        let out := Slice.proj (width + width') source shift
        if out.ok then some out else none
      else none
  | _, _ => none

abbrev Placed := Nat × Slice

/-- `acc` is newest-first. Merging walks toward older slices. -/
def addRev (acc : List Placed) (p : Placed) : Except MemError (List Placed) := do
  if !(decide (p.1 % 8 = 0)) then throw .badAlign
  if !p.2.ok then throw p.2.error
  match acc with
  | [] => pure [p]
  | last :: older =>
      if p.1 < last.1 + last.2.width then
        throw (.overlap p.1)
      else if p.1 == last.1 + last.2.width then
        match mergeSlice last.2 p.2 with
        | some merged => addRev older (last.1, merged)
        | none => pure (p :: last :: older)
      else
        pure (p :: last :: older)
termination_by acc.length

def insertSorted (p : Placed) : List Placed → List Placed
  | [] => [p]
  | q :: qs => if p.1 ≤ q.1 then p :: q :: qs else q :: insertSorted p qs

def sortPlaced (ps : List Placed) : List Placed :=
  ps.foldl (fun acc p => insertSorted p acc) []

def normalizePlaced (ps : List Placed) : Except MemError (List Placed) := do
  pure (← (sortPlaced ps).foldlM addRev []).reverse

def splitOne (atBit : Nat) (s : Slice) (lo hi : Nat) : Except MemError (List Placed) := do
  let stop := atBit + s.width
  if hi ≤ atBit || lo ≥ stop || lo ≥ hi then
    pure [(atBit, s)]
  else if lo ≤ atBit && stop ≤ hi then
    pure []
  else
    let mut out : List Placed := []
    if atBit < lo then
      out := out ++ [(atBit, ← subslice s 0 (lo - atBit))]
    if hi < stop then
      out := out ++ [(hi, ← subslice s (hi - atBit) (stop - hi))]
    pure out

def cut (ps : List Placed) (lo hi : Nat) : Except MemError (List Placed) :=
  ps.foldlM (fun acc (atBit, s) => do
    pure (acc ++ (← splitOne atBit s lo hi))) []

structure Tile where
  slices : List Slice
  deriving DecidableEq, BEq, Repr

def Tile.ok (tile : Tile) : Bool :=
  tile.slices.all Slice.ok

def Tile.width (tile : Tile) : Nat :=
  tile.slices.foldl (fun n s => n + s.width) 0

def place (start : Nat) (slices : List Slice) : Except MemError (List Placed) := do
  if !(decide (start % 8 = 0)) then throw .badAlign
  if slices.isEmpty then throw .empty
  let mut atBit := start
  let mut out : List Placed := []
  for s in slices do
    if !s.ok then throw s.error
    out := out ++ [(atBit, s)]
    atBit := atBit + s.width
  pure out

def normalizeTile (tile : Tile) : Except MemError Tile := do
  let placed ← normalizePlaced (← place 0 tile.slices)
  let mut atBit := 0
  let mut slices : List Slice := []
  for (start, s) in placed do
    if start ≠ atBit then throw (.gap atBit)
    slices := slices ++ [s]
    atBit := atBit + s.width
  pure ⟨slices⟩

inductive BitSlot where
  | stack
  | packet
  | context (field : Nat)
  | map (mapId : Nat) (key : Tile)
  deriving DecidableEq, BEq, Repr

def slotNorm : BitSlot → Except MemError BitSlot
  | .map mapId key => do pure (.map mapId (← normalizeTile key))
  | slot => pure slot

structure Mem where
  cells : List (BitSlot × List Placed)
  deriving DecidableEq, BEq, Repr

def Mem.empty : Mem := ⟨[]⟩

def Mem.find (mem : Mem) (slot : BitSlot) : List Placed :=
  match mem.cells.find? (fun cell => cell.1 == slot) with
  | some cell => cell.2
  | none => []

def Mem.store (mem : Mem) (slot : BitSlot) (ps : List Placed) : Mem :=
  ⟨(slot, ps) :: mem.cells.filter (fun cell => cell.1 != slot)⟩

def Mem.write (mem : Mem) (slot : BitSlot) (start : Nat) (tile : Tile) :
    Except MemError Mem := do
  let slot ← slotNorm slot
  let added ← place start tile.slices
  let stop := start + tile.width
  let kept ← cut (mem.find slot) start stop
  let slices ← normalizePlaced (kept ++ added)
  pure (mem.store slot slices)

def takeFrom : List Placed → Nat → Nat → Except MemError (List Slice)
  | [], need, hi => if need < hi then throw (.gap need) else pure []
  | (atBit, s) :: rest, need, hi => do
      if hi ≤ need then pure []
      else if atBit + s.width ≤ need then takeFrom rest need hi
      else if atBit > need then throw (.gap need)
      else
        let rel := need - atBit
        let clipHi := min (atBit + s.width) hi
        let head ← subslice s rel (clipHi - need)
        let tail ← takeFrom rest clipHi hi
        pure (head :: tail)

def Mem.read (mem : Mem) (slot : BitSlot) (lo hi : Nat) : Except MemError Tile := do
  if !(decide (lo % 8 = 0 ∧ hi > lo ∧ (hi - lo) % 8 = 0)) then throw .badAlign
  let slot ← slotNorm slot
  let placed ← normalizePlaced (mem.find slot)
  pure ⟨← takeFrom placed lo hi⟩

/-- Read the old interval, then replace it. A gap leaves the store unchanged. -/
def Mem.rmw (mem : Mem) (slot : BitSlot) (start : Nat) (tile : Tile) :
    Except MemError (Tile × Mem) := do
  let old ← mem.read slot start (start + tile.width)
  let mem ← mem.write slot start tile
  pure (old, mem)

structure MemWrite where
  slot : BitSlot
  start : Nat
  tile : Tile
  deriving DecidableEq, BEq, Repr

def Mem.apply (mem : Mem) (writes : List MemWrite) : Except MemError Mem :=
  writes.foldlM (fun m w => m.write w.slot w.start w.tile) mem

/-- A closed constant becomes one const slice. Anything else is a projection of that term. -/
def Tile.ofTerm (source : Term) (bits : Nat) : Except MemError Tile := do
  if !(decide (bits > 0 ∧ bits % 8 = 0 ∧ bits ≤ source.width.bits)) then throw .badWidth
  let slice := match eval (solve source) with
    | some c => Slice.const bits (c &&& ((1 <<< bits) - 1))
    | none => Slice.proj bits source 0
  if slice.ok then pure ⟨[slice]⟩ else throw slice.error

def sliceTerm : Slice → Term
  | .const w v =>
      if w ≤ 32 then zStar w .w64 32 (Term.C32 v) else Term.C64 v
  | .proj w source shift =>
      if shift == 0 && w == source.width.bits && source.width == .w64 then source
      else
        let field :=
          if shift == 0 && w == source.width.bits then source
          else star source.width (.extract shift w source.width.bits) [source]
        zStar w .w64 source.width.bits field

/-- One slice stays that slice's term. Several slices are little-endian pieces of one w64. -/
def Tile.toW64 (tile : Tile) : Except MemError Term := do
  if !(decide (tile.width > 0 ∧ tile.width ≤ 64)) then throw .badWidth
  match tile.slices with
  | [.const _ v] => pure (Term.C64 v)
  | [slice] => pure (sliceTerm slice)
  | slices =>
      let mut acc := Term.C64 0
      let mut shift := 0
      for s in slices do
        acc := orStar 64 .w64 acc (shlStar .w64 (sliceTerm s) (Term.C64 shift))
        shift := shift + s.width
      pure acc

/-- One slice's term. A full projection is that source. A field is an extract. -/
private def projectSlice : Slice → Term
  | .const width value =>
      if width ≤ 32 then Term.C32 value else Term.C64 value
  | .proj width source shift =>
      if shift == 0 && width == source.width.bits then source
      else if shift == 0 then star source.width (.low width source.width.bits) [source]
      else star source.width (.extract shift width source.width.bits) [source]

/-- Assemble a tile into one term. Adjacent constant slices should already be merged. -/
def Tile.project (tile : Tile) : Except MemError Term := do
  if !(decide (tile.width > 0 ∧ tile.width ≤ 64)) then throw .badWidth
  match tile.slices with
  | [] => throw .empty
  | [s] => pure (projectSlice s)
  | slices =>
      let w : Width := if tile.width ≤ 32 then .w32 else .w64
      let mut acc := Term.C w 0
      let mut atBit := 0
      for s in slices do
        let part := projectSlice s
        acc := orStar w.bits w acc
          (shlStar w (zStar s.width w part.width.bits part) (Term.C w atBit))
        atBit := atBit + s.width
      pure acc

/-- Copied key bytes, little-endian, one slice per byte. This is the map key. -/
def keyTile (bytes : List Term) : Except MemError Tile := do
  if bytes.isEmpty then throw .empty
  let mut slices : List Slice := []
  for t in bytes do
    let one ← Tile.ofTerm t 8
    slices := slices ++ one.slices
  normalizeTile ⟨slices⟩

/-- Place a `bits`-wide field into a destination of width `w`. -/
def fitBits (bits : Nat) (w : Width) (signed : Bool) (field : Term) : Term :=
  if bits == field.width.bits && field.width == w then field
  else if signed then sStar bits w field.width.bits field
  else zStar bits w field.width.bits field

instance : Inhabited Slice where
  default := .const 8 0

instance : Inhabited Tile where
  default := ⟨[]⟩

instance : Inhabited BitSlot where
  default := .stack

instance : Inhabited Mem where
  default := .empty

instance : Inhabited MemWrite where
  default := ⟨.stack, 0, default⟩

def sliceKey : Slice → List Nat
  | .const w v => [0, w, v]
  | .proj w source shift => [1, w, shift] ++ source.orderKey

def BitSlot.key : BitSlot → List Nat
  | .stack => [0]
  | .packet => [1]
  | .context field => [2, field]
  | .map id key => [3, id] ++ key.slices.flatMap sliceKey

def Mem.canonical (mem : Mem) : Mem :=
  ⟨mem.cells.mergeSort (fun a b => decide (a.1.key ≤ b.1.key))⟩

def ownerCount (ps : List Placed) (bit : Nat) : Nat :=
  ps.foldl (fun n (atBit, s) =>
    if decide (atBit ≤ bit ∧ bit < atBit + s.width) then n + 1 else n) 0

private def okTile (x : Except MemError Tile) (tile : Tile) : Bool :=
  match x with
  | .ok got => got == tile
  | .error _ => false

private def errIs {α : Type} (x : Except MemError α) (error : MemError) : Bool :=
  match x with
  | .error got => got == error
  | .ok _ => false

private def wrote (slot : BitSlot) (start : Nat) (tile : Tile) (mem : Mem := .empty) :
    Except MemError Mem :=
  mem.write slot start tile

#guard errIs (Mem.write .empty .stack 0 ⟨[.const 7 1]⟩) .badWidth
#guard errIs (Mem.write .empty .stack 0 ⟨[.const 8 256]⟩) .badConst
#guard errIs (Mem.write .empty .stack 4 ⟨[.const 8 1]⟩) .badAlign
#guard errIs (Mem.read .empty .stack 1 9) .badAlign
#guard errIs (Mem.read .empty .stack 0 4) .badAlign
#guard errIs (Mem.write .empty (.map 1 ⟨[.const 7 1]⟩) 0 ⟨[.const 8 1]⟩) .badWidth
#guard errIs
  (Mem.write ⟨[(.stack, [(0, .const 16 1), (8, .const 16 2)])]⟩ .stack 0 ⟨[.const 8 3]⟩)
  (.overlap 8)
#guard errIs (Mem.write .empty .stack 0 ⟨[.proj 8 (Term.V32 0) 1]⟩) .badAlign
#guard errIs (Mem.write .empty .stack 0 ⟨[.proj 16 (Term.V32 0) 24]⟩) .badWidth
#guard errIs (Mem.write .empty .stack 0 ⟨[]⟩) .empty

#guard match wrote .stack 0 ⟨[.const 32 0xAABBCCDD]⟩ with
  | .ok mem =>
      okTile (mem.read .stack 0 32) ⟨[.const 32 0xAABBCCDD]⟩ &&
        match mem.write .stack 8 ⟨[.const 8 0x11]⟩ with
        | .ok mem => okTile (mem.read .stack 0 32) ⟨[.const 32 0xAABB11DD]⟩
        | .error _ => false
  | .error _ => false

#guard match wrote .stack 0 ⟨[.proj 32 (Term.V32 7) 0]⟩ with
  | .ok mem =>
      match mem.write .stack 8 ⟨[.const 8 0x11]⟩ with
      | .ok mem =>
          okTile (mem.read .stack 0 32)
            ⟨[.proj 8 (Term.V32 7) 0, .const 8 0x11, .proj 16 (Term.V32 7) 16]⟩ &&
            (List.range 32).all (fun bit =>
              ownerCount (mem.find .stack) bit == 1)
      | .error _ => false
  | .error _ => false

#guard match wrote .stack 0 ⟨[.proj 8 (Term.V32 1) 0]⟩ with
  | .ok mem =>
      match mem.write .stack 8 ⟨[.proj 8 (Term.V32 1) 16]⟩ with
      | .ok mem =>
          okTile (mem.read .stack 0 16)
            ⟨[.proj 8 (Term.V32 1) 0, .proj 8 (Term.V32 1) 16]⟩
      | .error _ => false
  | .error _ => false

#guard match wrote .stack 0 ⟨[.proj 8 (Term.V32 1) 0]⟩ with
  | .ok mem =>
      match mem.write .stack 8 ⟨[.proj 8 (Term.V32 2) 0]⟩ with
      | .ok mem =>
          okTile (mem.read .stack 0 16)
            ⟨[.proj 8 (Term.V32 1) 0, .proj 8 (Term.V32 2) 0]⟩
      | .error _ => false
  | .error _ => false

#guard match wrote .stack 0 ⟨[.const 8 1]⟩ with
  | .ok mem => errIs (mem.read .stack 0 16) (.gap 8)
  | .error _ => false

#guard match wrote .stack 0 ⟨[.const 32 0xAABBCCDD]⟩ with
  | .ok mem =>
      errIs (mem.read .stack 32 40) (.gap 32) &&
        match mem.write .stack 24 ⟨[.const 16 0x1234]⟩ with
        | .ok mem =>
            okTile (mem.read .stack 0 40)
              ⟨[.const 40 (0xBBCCDD + (0x1234 <<< 24))]⟩ &&
              okTile (mem.read .stack 32 40) ⟨[.const 8 ((0x1234 >>> 8) &&& 0xff)]⟩
        | .error _ => false
  | .error _ => false

#guard match wrote .stack 0 ⟨[.proj 32 (Term.V32 7) 0]⟩ with
  | .ok mem =>
      match mem.rmw .stack 8 ⟨[.const 8 0x11]⟩ with
      | .ok (old, mem) =>
          old == ⟨[.proj 8 (Term.V32 7) 8]⟩ &&
            okTile (mem.read .stack 0 32)
              ⟨[.proj 8 (Term.V32 7) 0, .const 8 0x11, .proj 16 (Term.V32 7) 16]⟩
      | .error _ => false
  | .error _ => false

#guard errIs (Mem.rmw .empty .stack 0 ⟨[.const 8 1]⟩) (.gap 0)

#guard match wrote .stack 0 ⟨[.const 8 1]⟩ with
  | .ok mem =>
      match wrote .packet 0 ⟨[.const 8 2]⟩ mem with
      | .ok mem =>
          okTile (mem.read .stack 0 8) ⟨[.const 8 1]⟩ &&
            okTile (mem.read .packet 0 8) ⟨[.const 8 2]⟩
      | .error _ => false
  | .error _ => false

#guard match wrote (.context 0) 0 ⟨[.const 8 1]⟩ with
  | .ok mem =>
      match wrote (.context 1) 0 ⟨[.const 8 2]⟩ mem with
      | .ok mem =>
          okTile (mem.read (.context 0) 0 8) ⟨[.const 8 1]⟩ &&
            errIs (mem.read (.context 1) 8 16) (.gap 8)
      | .error _ => false
  | .error _ => false

#guard
  let keyOne : Tile := ⟨[.const 16 0x0201]⟩
  let keySplit : Tile := ⟨[.const 8 0x01, .const 8 0x02]⟩
  match wrote (.map 3 keySplit) 0 ⟨[.const 8 9]⟩ with
  | .ok mem => okTile (mem.read (.map 3 keyOne) 0 8) ⟨[.const 8 9]⟩
  | .error _ => false

#guard
  let keyA : Tile := ⟨[.const 8 1]⟩
  let keyB : Tile := ⟨[.const 8 2]⟩
  match wrote (.map 3 keyA) 0 ⟨[.const 8 9]⟩ with
  | .ok mem =>
      match wrote (.map 3 keyB) 0 ⟨[.const 8 8]⟩ mem with
      | .ok mem =>
          okTile (mem.read (.map 3 keyA) 0 8) ⟨[.const 8 9]⟩ &&
            okTile (mem.read (.map 3 keyB) 0 8) ⟨[.const 8 8]⟩
      | .error _ => false
  | .error _ => false

#guard errIs
  (Mem.read ⟨[(.stack, [(0, .const 16 1), (8, .const 16 2)])]⟩ .stack 0 16)
  (.overlap 8)

end Core
