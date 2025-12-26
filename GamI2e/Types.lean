/-
Core type definitions for the GAM/I2E memory model formalization.

This module defines the basic types used throughout the formalization:
- Memory addresses and values
- Register identifiers
- Instruction types
-/

namespace GamI2e

/-- Memory addresses -/
def Addr := Nat
deriving DecidableEq, Repr

instance : OfNat Addr n where
  ofNat := n

/-- Memory values -/
def Value := Nat
deriving DecidableEq, Repr

instance : OfNat Value n where
  ofNat := n

/-- Register identifiers -/
def RegId := Nat
deriving DecidableEq, Repr

/-- Processor identifiers -/
def ProcId := Nat
deriving DecidableEq, Repr, LT, LE

/-- Instruction identifiers (unique across all processors) -/
def InstId := Nat
deriving DecidableEq, Repr

/-- Address operand: either a literal or computed from registers -/
inductive AddrOperand where
  | literal : Addr → AddrOperand                    -- Literal address: a
  | regOffset : RegId → Addr → AddrOperand          -- Register + offset: rs + offset
  | regSum : RegId → RegId → Addr → AddrOperand    -- Two registers + offset: rs1 + rs2 + offset
deriving DecidableEq, Repr

/-- Data operand for stores: either a literal or from a register -/
inductive DataOperand where
  | literal : Value → DataOperand     -- Literal value
  | register : RegId → DataOperand    -- Value from register
deriving DecidableEq, Repr

/-- Fence kinds for fine-grained memory barriers.

    From the paper (Tables 2, 4, 5):
    - **RMO** uses FenceLL, FenceLS, FenceSL, FenceSS (4 separate fences)
    - **WMM** uses Commit (release), Reconcile (acquire)
    - **RISC-V** uses combinations like fence.r.r, fence.r.w, fence.w.r, fence.w.w

    The encoding here supports:
    - Individual direction fences (LL, LS, SL, SS)
    - Full fence (all directions)
    - Acquire/Release semantics (for WMM-style models)

    Note: A fence can enforce multiple orderings. For example, TSO's fence
    is essentially a Store-Load fence (fenceSL), while a full fence
    enforces all four orderings. -/
inductive FenceKind where
  | fenceLL : FenceKind   -- Orders Load-Load (prevents load reordering)
  | fenceLS : FenceKind   -- Orders Load-Store (prevents load-store reordering)
  | fenceSL : FenceKind   -- Orders Store-Load (prevents store-load reordering, strongest)
  | fenceSS : FenceKind   -- Orders Store-Store (prevents store reordering)
  | full    : FenceKind   -- Full fence: orders all memory operations
  -- WMM-style fences (can be modeled as combinations, but useful to have)
  | acquire : FenceKind   -- Acquire: orders subsequent reads/writes after this (like LL + LS)
  | release : FenceKind   -- Release: orders prior reads/writes before this (like SL + SS)
deriving DecidableEq, Repr

/-- Instruction types as described in the paper.
    Examples from paper:
    - r1 = Ld a             (load from literal address)
    - r2 = Ld (b+r1-r1)     (load from computed address)
    - St b = r1             (store register to address)
    - St b = 1              (store literal to address)
    - Fence                 (memory barrier)

    Note: Fence instructions are parameterized by FenceKind to support
    different memory models (RMO, WMM, ARM, RISC-V) which have different
    fence types with varying ordering guarantees. -/
inductive InstType where
  | load    : AddrOperand → RegId → InstType        -- Load from address to register
  | store   : AddrOperand → DataOperand → InstType  -- Store data to address
  | regOp   : RegId → RegId → RegId → InstType      -- Reg-to-reg operation (rd = rs1 op rs2)
  | branch  : RegId → Addr → InstType               -- Branch based on register to address
  | fence   : FenceKind → InstType                  -- Fence instruction with specific kind
deriving DecidableEq, Repr

/-- An instruction with a unique identifier and processor id -/
structure Instruction where
  id : InstId
  procId : ProcId
  instType : InstType
deriving DecidableEq, Repr

/-- Default address operand -/
instance : Inhabited AddrOperand where
  default := .literal 0

/-- Default data operand -/
instance : Inhabited DataOperand where
  default := .literal 0

/-- Default instruction (full fence with id 0 on processor 0) -/
instance : Inhabited Instruction where
  default := { id := (0 : Nat), procId := (0 : Nat), instType := .fence .full }

/-- Check if an instruction is a memory instruction (load or store) -/
def Instruction.isMemInst (i : Instruction) : Bool :=
  match i.instType with
  | .load _ _ => true
  | .store _ _ => true
  | _ => false

/-- Check if an instruction is a load -/
def Instruction.isLoad (i : Instruction) : Bool :=
  match i.instType with
  | .load _ _ => true
  | _ => false

/-- Check if an instruction is a store -/
def Instruction.isStore (i : Instruction) : Bool :=
  match i.instType with
  | .store _ _ => true
  | _ => false

/-- Check if an instruction is a fence -/
def Instruction.isFence (i : Instruction) : Bool :=
  match i.instType with
  | .fence _ => true
  | _ => false

/-- Get the fence kind of an instruction (if it's a fence) -/
def Instruction.fenceKind? (i : Instruction) : Option FenceKind :=
  match i.instType with
  | .fence fk => some fk
  | _ => none

/-- Check if an instruction is a branch -/
def Instruction.isBranch (i : Instruction) : Bool :=
  match i.instType with
  | .branch _ _ => true
  | _ => false

/-- Get registers used in an address operand -/
def AddrOperand.registers (ao : AddrOperand) : List RegId :=
  match ao with
  | .literal _ => []
  | .regOffset r _ => [r]
  | .regSum r1 r2 _ => [r1, r2]

/-- Get the memory address of a memory instruction (if it's a literal).
    Note: For computed addresses, this returns none until the address is computed. -/
def Instruction.getAddr? (i : Instruction) : Option Addr :=
  match i.instType with
  | .load ao _ =>
    match ao with
    | .literal a => some a
    | _ => none
  | .store ao _ =>
    match ao with
    | .literal a => some a
    | _ => none
  | _ => none

/-- Check if two memory instructions access the same address (if both are literals) -/
def Instruction.sameAddr (i1 i2 : Instruction) : Bool :=
  match i1.getAddr?, i2.getAddr? with
  | some a1, some a2 => a1 == a2
  | _, _ => false

/-- Check if an address operand is a literal (not computed from registers) -/
def AddrOperand.isLiteral (ao : AddrOperand) : Bool :=
  match ao with
  | .literal _ => true
  | .regOffset _ _ => false
  | .regSum _ _ _ => false

/-- Check if a data operand is a literal -/
def DataOperand.isLiteral (do_ : DataOperand) : Bool :=
  match do_ with
  | .literal _ => true
  | .register _ => false

/-- Check if an instruction uses only literal addresses.
    Non-memory instructions trivially satisfy this. -/
def Instruction.hasLiteralAddr (i : Instruction) : Bool :=
  match i.instType with
  | .load ao _ => ao.isLiteral
  | .store ao _ => ao.isLiteral
  | _ => true

/-- For memory instructions with literal addresses, getAddr? returns Some.
    This is the key property that makes literal-address programs tractable. -/
theorem Instruction.hasLiteralAddr_getAddr_some (i : Instruction) :
    i.isMemInst → i.hasLiteralAddr → ∃ a, i.getAddr? = some a := by
  intro h_mem h_lit
  cases i with
  | mk id procId instType =>
    cases instType with
    | load ao rd =>
      simp only [hasLiteralAddr, AddrOperand.isLiteral] at h_lit
      cases ao with
      | literal a =>
        exact ⟨a, rfl⟩
      | regOffset r off =>
        simp at h_lit
      | regSum r1 r2 off =>
        simp at h_lit
    | store ao data =>
      simp only [hasLiteralAddr, AddrOperand.isLiteral] at h_lit
      cases ao with
      | literal a =>
        exact ⟨a, rfl⟩
      | regOffset r off =>
        simp at h_lit
      | regSum r1 r2 off =>
        simp at h_lit
    | regOp rd rs1 rs2 =>
      simp only [isMemInst] at h_mem
      cases h_mem
    | branch r target =>
      simp only [isMemInst] at h_mem
      cases h_mem
    | fence _ =>
      simp only [isMemInst] at h_mem
      cases h_mem

/-- Get the read set of an instruction (all registers read) -/
def Instruction.readSet (i : Instruction) : List RegId :=
  match i.instType with
  | .load ao _ => ao.registers
  | .store ao data =>
    let addrRegs := ao.registers
    let dataRegs := match data with
      | .literal _ => []
      | .register r => [r]
    addrRegs ++ dataRegs
  | .regOp _ rs1 rs2 => [rs1, rs2]
  | .branch r _ => [r]
  | .fence _ => []

/-- Get the write set of an instruction (registers written) -/
def Instruction.writeSet (i : Instruction) : List RegId :=
  match i.instType with
  | .load _ rd => [rd]
  | .store _ _ => []
  | .regOp rd _ _ => [rd]
  | .branch _ _ => []
  | .fence _ => []

/-- Get the address read set (registers used for address computation) -/
def Instruction.addrReadSet (i : Instruction) : List RegId :=
  match i.instType with
  | .load ao _ => ao.registers
  | .store ao _ => ao.registers
  | _ => []

/-- Theorem: Address read set is a subset of read set.
    This is the ISA property mentioned in the paper:
    "data-dependency includes addr-dependency".

    The paper doesn't need to axiomatize this - it follows from the definition of
    RS (all registers read) and ARS (registers for address computation), since
    address computation registers must be read by the instruction.

    Proof by case analysis on instruction type:
    - For loads: addrReadSet = ao.registers, readSet = ao.registers (identical)
    - For stores: addrReadSet = ao.registers, readSet = ao.registers ++ dataRegs (prefix)
    - For non-memory: addrReadSet = [] (vacuously true) -/
theorem addrReadSet_subset_readSet : ∀ (i : Instruction) (r : RegId),
  r ∈ i.addrReadSet → r ∈ i.readSet := by
  intro i r h
  cases i with
  | mk id procId instType =>
    cases instType with
    | load ao rd =>
      unfold Instruction.addrReadSet at h
      unfold Instruction.readSet
      exact h
    | store ao data =>
      unfold Instruction.addrReadSet at h
      unfold Instruction.readSet
      apply List.mem_append_left
      exact h
    | regOp rd rs1 rs2 =>
      unfold Instruction.addrReadSet at h
      cases h
    | branch r_cond target =>
      unfold Instruction.addrReadSet at h
      cases h
    | fence _ =>
      unfold Instruction.addrReadSet at h
      cases h

/-! ## Address Assignment

The paper's model allows memory addresses to be computed from register values at runtime
(e.g., `Ld r1` where `r1` contains the address). To support this, we parameterize
relations by an "address assignment" that maps instructions to their computed addresses.

This allows the axiomatic model to reason about same-address relationships without
knowing the actual register values - those are provided by the address assignment,
which can be extracted from an operational execution.
-/

/-- An address assignment maps instruction IDs to their computed addresses.
    This is used to parameterize relations that need runtime address information.

    - For literal-address instructions, the assignment should match `getAddr?`
    - For register-computed addresses, the assignment provides the runtime value
    - For non-memory instructions, the assignment returns `none` -/
def AddressAssignment := InstId → Option Addr

/-- Default address assignment: extracts literal addresses, returns none otherwise -/
def AddressAssignment.fromLiterals : AddressAssignment :=
  fun _ => none  -- In practice, would need instruction lookup

/-- Check if two instructions access the same address using an address assignment.
    Returns false if either instruction's address is unknown. -/
def Instruction.sameAddrWith (aa : AddressAssignment) (i1 i2 : Instruction) : Bool :=
  match aa i1.id, aa i2.id with
  | some a1, some a2 => a1 == a2
  | _, _ => false

/-- Get the address of an instruction using an address assignment -/
def Instruction.getAddrWith (aa : AddressAssignment) (i : Instruction) : Option Addr :=
  aa i.id

/-- An address assignment is consistent with literal addresses if it agrees with getAddr?
    for all instructions that have literal addresses. -/
def AddressAssignment.consistentWithLiterals (aa : AddressAssignment) (insts : List Instruction) : Prop :=
  ∀ i ∈ insts, i.hasLiteralAddr → aa i.id = i.getAddr?

/-- For literal-address programs, sameAddrWith agrees with sameAddr when using a consistent assignment -/
theorem sameAddrWith_eq_sameAddr_of_literal
    (aa : AddressAssignment) (i1 i2 : Instruction)
    (_h1 : i1.hasLiteralAddr) (_h2 : i2.hasLiteralAddr)
    (hc1 : aa i1.id = i1.getAddr?) (hc2 : aa i2.id = i2.getAddr?) :
    i1.sameAddrWith aa i2 = i1.sameAddr i2 := by
  simp only [Instruction.sameAddrWith, Instruction.sameAddr, hc1, hc2]

/-- An address assignment covers all memory instructions in a list -/
def AddressAssignment.coversAll (aa : AddressAssignment) (insts : List Instruction) : Prop :=
  ∀ i ∈ insts, i.isMemInst → (aa i.id).isSome

/-- An address assignment is well-formed if it only assigns addresses to memory instructions.
    This property ensures that having an address implies being a memory instruction. -/
def AddressAssignment.onlyMemInst (aa : AddressAssignment) (insts : List Instruction) : Prop :=
  ∀ i ∈ insts, (aa i.id).isSome → i.isMemInst

/-- For a well-formed address assignment, having an address implies being a load or store -/
theorem hasAddr_implies_memInst_of_wellformed (aa : AddressAssignment) (insts : List Instruction) (i : Instruction)
    (h_wf : aa.onlyMemInst insts) (h_mem : i ∈ insts) (h_addr : (aa i.id).isSome) :
    i.isMemInst = true :=
  h_wf i h_mem h_addr

/-- Memory instructions are exactly loads or stores -/
theorem isMemInst_iff_load_or_store (i : Instruction) :
    i.isMemInst = true ↔ (i.isLoad = true ∨ i.isStore = true) := by
  unfold Instruction.isMemInst Instruction.isLoad Instruction.isStore
  cases i.instType <;> simp

end GamI2e
