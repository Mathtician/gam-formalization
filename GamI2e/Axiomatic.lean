/-
GAM Axiomatic Model

This module defines the axiomatic semantics of the GAM memory model.
The axiomatic model takes an execution witness as input, which includes:
- Program order (po)
- Memory order (mo)
- Address assignment (aa)
- Read-from relation (rf)

And checks them against two axioms:
- Inst-Order: Memory order respects preserved program order
- Load-Value: Loads read from the correct stores
-/

import GamI2e.Types
import GamI2e.Relations
import GamI2e.Ordering
import GamI2e.PreservedPO

namespace GamI2e

/-- An execution witness consists of program order, memory order, address assignment,
    and read-from relations -/
structure ExecutionWitness where
  /-- Program order: per-processor total order -/
  po : ProgramOrder
  /-- Memory order: total order of all memory instructions -/
  mo : MemoryOrder
  /-- Address assignment: computed addresses for all memory instructions -/
  aa : AddressAssignment
  /-- Read-from: relates stores to loads -/
  rf : ReadFrom aa

/-- A program execution consists of a list of instructions per processor -/
structure ProgramExecution where
  /-- Number of processors -/
  numProcs : Nat
  /-- Instructions for each processor (indexed by processor ID) -/
  instructions : ProcId → List Instruction
  /-- All instructions have correct processor IDs -/
  procId_correct : ∀ p inst, inst ∈ instructions p → inst.procId = p

/-- Extract all instructions from a program execution -/
def ProgramExecution.allInstructions (prog : ProgramExecution) : List Instruction :=
  (List.range prog.numProcs).flatMap (fun p => prog.instructions p)

/-- Check if an execution witness is consistent with a program execution -/
def ExecutionWitness.consistentWith (ew : ExecutionWitness) (prog : ProgramExecution) : Prop :=
  -- Program order only relates instructions in the program
  (∀ i j : Instruction, ew.po.rel i j →
    i ∈ prog.allInstructions ∧ j ∈ prog.allInstructions) ∧
  -- Program order matches the instruction ordering in each processor
  (∀ p, ∀ i j : Instruction,
    i ∈ prog.instructions p →
    j ∈ prog.instructions p →
    i.procId = p →
    j.procId = p →
    (ew.po.rel i j ↔
     ∃ idx_i idx_j,
       (prog.instructions p)[idx_i]! = i ∧
       (prog.instructions p)[idx_j]! = j ∧
       idx_i < idx_j ∧
       idx_i < (prog.instructions p).length ∧
       idx_j < (prog.instructions p).length))

/-- Check if the Inst-Order axiom holds -/
def satisfies_InstOrder (of : OrderedFunc) (ew : ExecutionWitness) : Prop :=
  ∀ (i1 i2 : Instruction),
    preservedProgramOrder ew.aa of ew.po i1 i2 →
    i1.isMemInst →
    i2.isMemInst →
    ew.mo.rel i1 i2

/-- Check if the Load-Value axiom holds -/
def satisfies_LoadValue (ew : ExecutionWitness) : Prop :=
  ∀ (s l : Instruction) (a : Addr),
    -- Both instructions access address a (via address assignment)
    ew.aa s.id = some a →
    ew.aa l.id = some a →
    s.isStore →
    l.isLoad →
    ew.rf.rel s l →
    -- Two requirements:
    -- 1. S must be visible (in the candidate set)
    (ew.po.rel s l ∨ ew.mo.rel s l) ∧
    -- 2. S must be the youngest visible store
    (∀ s' : Instruction,
      s'.isStore →
      ew.aa s'.id = some a →
      (ew.po.rel s' l ∨ ew.mo.rel s' l) →
      (ew.mo.rel s' s ∨ s' = s))

/-- A program execution is legal under GAM if there exists a witness satisfying the axioms -/
def GAM_Legal (of : OrderedFunc) (prog : ProgramExecution) : Prop :=
  ∃ (ew : ExecutionWitness),
    -- Address assignment covers all memory instructions
    ew.aa.coversAll prog.allInstructions ∧
    -- Witness is consistent with program
    ew.consistentWith prog ∧
    -- Axioms are satisfied
    satisfies_InstOrder of ew ∧
    satisfies_LoadValue ew

/-- Helper: get the value written by a store (if it's a literal) -/
def Instruction.getStoreValue? (i : Instruction) : Option Value :=
  match i.instType with
  | .store _ (.literal v) => some v
  | _ => none

/-- Helper: get the destination register of a load -/
def Instruction.getLoadDest? (i : Instruction) : Option RegId :=
  match i.instType with
  | .load _ rd => some rd
  | _ => none

/-- Reformulation of Load-Value axiom in a more usable form.
    Given that the witness satisfies the Load-Value axiom, we can extract
    the property for a specific load and store. -/
theorem loadValue_iff (ew : ExecutionWitness)
    (s l : Instruction) (a : Addr) :
    satisfies_LoadValue ew →
    ew.rf.rel s l →
    s.isStore →
    l.isLoad →
    ew.aa s.id = some a →
    ew.aa l.id = some a →
    -- Then s is visible and mo-maximal
    (ew.po.rel s l ∨ ew.mo.rel s l) ∧
    (∀ s' : Instruction,
      s'.isStore →
      ew.aa s'.id = some a →
      (ew.po.rel s' l ∨ ew.mo.rel s' l) →
      ew.mo.rel s' s ∨ s' = s) := by
  intro h_loadValue h_rf h_store h_load h_addr_s h_addr_l
  exact h_loadValue s l a h_addr_s h_addr_l h_store h_load h_rf

/-- The Inst-Order axiom is just the unfolded definition -/
theorem instOrder_unfold (of : OrderedFunc) (ew : ExecutionWitness) :
    satisfies_InstOrder of ew ↔
    (∀ i1 i2,
      preservedProgramOrder ew.aa of ew.po i1 i2 →
      i1.isMemInst → i2.isMemInst →
      ew.mo.rel i1 i2) := by
  simp [satisfies_InstOrder]

/-- Memory order is acyclic (follows from being a total order) -/
theorem mo_acyclic (ew : ExecutionWitness) :
    acyclic ew.mo.rel := by
  intro i h
  cases h with
  | single h_edge =>
    exact ew.mo.irrefl i h_edge
  | tail h_rest h_last =>
    induction h_rest with
    | single h_first =>
      have : ew.mo.rel i i := ew.mo.trans i _ i h_first h_last
      exact ew.mo.irrefl i this
    | tail h_inner h_mid ih =>
      rename_i b c
      have h_b_i : ew.mo.rel b i := ew.mo.trans b c i h_mid h_last
      exact ih h_b_i

/-- Helper: lifting through TransGen -/
private theorem transGen_lift {α : Type _} (r1 r2 : α → α → Prop)
    (h : ∀ x y, r1 x y → r2 x y) :
    ∀ x y, Relation.TransGen r1 x y → Relation.TransGen r2 x y := by
  intro x y h_trans
  induction h_trans with
  | single h_edge =>
    exact Relation.TransGen.single (h _ _ h_edge)
  | tail h_rest h_last ih =>
    exact Relation.TransGen.tail ih (h _ _ h_last)

/-- If mo contains ppo, then mo is acyclic implies ppo is acyclic -/
theorem ppo_acyclic_from_mo (of : OrderedFunc) (ew : ExecutionWitness) :
    (∀ i1 i2, preservedProgramOrder ew.aa of ew.po i1 i2 → ew.mo.rel i1 i2) →
    acyclic (preservedProgramOrder ew.aa of ew.po) := by
  intro h_ppo_in_mo i h_cycle
  have h_mo_cycle : Relation.TransGen ew.mo.rel i i :=
    @transGen_lift Instruction (preservedProgramOrder ew.aa of ew.po) ew.mo.rel h_ppo_in_mo i i h_cycle
  exact mo_acyclic ew i h_mo_cycle

/-- If po.rel holds and consistentWith holds, then the first instruction
    is in allInstructions -/
theorem po_rel_implies_mem_allInstructions_fst
    (ew : ExecutionWitness) (prog : ProgramExecution)
    (i1 i2 : Instruction) :
    ew.consistentWith prog →
    ew.po.rel i1 i2 →
    i1 ∈ prog.allInstructions := by
  intro h_cons h_po
  exact (h_cons.1 i1 i2 h_po).1

/-- If po.rel holds and consistentWith holds, then the second instruction
    is in allInstructions -/
theorem po_rel_implies_mem_allInstructions_snd
    (ew : ExecutionWitness) (prog : ProgramExecution)
    (i1 i2 : Instruction) :
    ew.consistentWith prog →
    ew.po.rel i1 i2 →
    i2 ∈ prog.allInstructions := by
  intro h_cons h_po
  exact (h_cons.1 i1 i2 h_po).2

end GamI2e
