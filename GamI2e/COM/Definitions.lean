/-
COM: Alternative Axiomatic Model - Basic Definitions

This module defines the COM (Communication) axiomatic model,
which is an alternative formulation of GAM that is more suitable
for model checking tools.

The COM model uses:
- Coherence order (co): per-address total order of stores
- From-reads (fr): derived from rf and co
- Program order same location (poloc)

And has two axioms:
- SC-per-Location: Acyclicity of rf ∪ co ∪ fr ∪ poloc
- Causality: Acyclicity of rfe ∪ co ∪ fr ∪ ppo
-/

import GamI2e.Types
import GamI2e.Relations
import GamI2e.Ordering
import GamI2e.PreservedPO
import GamI2e.Axiomatic

namespace GamI2e

/-- Axiom SC-per-Location: Sequential consistency per memory location
    The union rf ∪ co ∪ fr ∪ poloc must be acyclic -/
def COM_scPerLocation (ew : ExecutionWitness) : Prop :=
  let co := coherenceOrderAll ew.aa ew.mo
  let fr := fromReads ew.aa ew.rf ew.mo
  let poloc := programOrderLoc ew.aa ew.po
  acyclic (unionRel (unionRel (unionRel ew.rf.rel co) fr) poloc)

/-- The causality relation: rfe ∪ co ∪ fr ∪ ppo -/
def causalityRel (of : OrderedFunc) (ew : ExecutionWitness) : Relation :=
  let co := coherenceOrderAll ew.aa ew.mo
  let fr := fromReads ew.aa ew.rf ew.mo
  let rfe := readFromExternal ew.aa ew.rf
  let ppo := preservedProgramOrder ew.aa of ew.po
  unionRel (unionRel (unionRel rfe co) fr) ppo

/-- Axiom Causality: The union rfe ∪ co ∪ fr ∪ ppo must be acyclic -/
def COM_causality (of : OrderedFunc) (ew : ExecutionWitness) : Prop :=
  acyclic (causalityRel of ew)

/-- COM Axiomatic Model: Alternative formulation using communication relations -/
def COM_Legal (of : OrderedFunc) (ew : ExecutionWitness) : Prop :=
  COM_scPerLocation ew ∧ COM_causality of ew

/-- Extended communication order: eco = co ∪ fr ∪ co*;rf ∪ rf⁻¹;co*;rf

Following the paper (ComProofs.tex, definition before Lemma 3):
- co (Write to Write): coherence order between stores
- fr (Read to Write): from-reads relation
- co*;rf (Write to Read): store reaches load via co* then rf
- rf⁻¹;co*;rf (Read to Read): load reaches load via rf⁻¹, co*, rf

Note: eco is NOT irreflexive! With co* in rf⁻¹;co*;rf, we have rf⁻¹;rf (via
empty co path), which relates any load to itself. This is fine - the paper's
proof doesn't require eco irreflexivity. Instead, it uses eco_total and eco_poloc
to reduce cycles, ultimately showing they reduce to co-only cycles. -/
def extendedCommunication (ew : ExecutionWitness) : Relation :=
  let co := coherenceOrderAll ew.aa ew.mo
  let fr := fromReads ew.aa ew.rf ew.mo
  let co_star_rf := composeRel (reflTransClosure co) ew.rf.rel  -- co*;rf (includes rf)
  let rf_co_star_rf := composeRel (inverseRel ew.rf.rel)        -- rf⁻¹;co*;rf
                         (composeRel (reflTransClosure co) ew.rf.rel)
  unionRel (unionRel (unionRel co fr) co_star_rf) rf_co_star_rf

/-- Helper: check if instruction is a store -/
private def isStoreAt (aa : AddressAssignment) (i : Instruction) (a : Addr) : Prop :=
  i.isStore = true ∧ aa i.id = some a

/-- Helper: check if instruction is a load -/
private def isLoadAt (aa : AddressAssignment) (i : Instruction) (a : Addr) : Prop :=
  i.isLoad = true ∧ aa i.id = some a

/-- Helper lemma: stores are memory instructions -/
theorem isStore_implies_isMemInst (i : Instruction) :
    i.isStore = true → i.isMemInst = true := by
  intro h_store
  unfold Instruction.isMemInst Instruction.isStore at *
  cases h : i.instType <;> simp [h] at h_store <;> rfl

/-- Helper lemma: loads are memory instructions -/
theorem isLoad_implies_isMemInst (i : Instruction) :
    i.isLoad = true → i.isMemInst = true := by
  intro h_load
  unfold Instruction.isMemInst Instruction.isLoad at *
  cases h : i.instType <;> simp [h] at h_load <;> rfl

/-- Helper: instruction with address must be either load or store
    For a well-formed address assignment, having an address implies being a memory instruction,
    which in turn means being either a load or a store. -/
theorem hasAddr_implies_load_or_store (aa : AddressAssignment) (insts : List Instruction)
    (h_wf : aa.onlyMemInst insts) (i : Instruction) (h_mem : i ∈ insts) :
    (aa i.id).isSome → i.isLoad = true ∨ i.isStore = true := by
  intro h_has_addr
  -- First, use well-formedness to show i is a memory instruction
  have h_is_mem : i.isMemInst = true := hasAddr_implies_memInst_of_wellformed aa insts i h_wf h_mem h_has_addr
  -- Then use the equivalence: isMemInst ↔ (isLoad ∨ isStore)
  rw [isMemInst_iff_load_or_store] at h_is_mem
  exact h_is_mem

/-- Helper: extract address from rf witness and prove it equals the load's address -/
theorem rf_same_addr (ew : ExecutionWitness) (w l : Instruction) (a : Addr)
    (h_rf : ew.rf.rel w l) (h_addr_l : ew.aa l.id = some a) :
    ew.aa w.id = some a := by
  have h_same := ew.rf.sameAddr w l h_rf
  simp [Instruction.sameAddrWith] at h_same
  cases h_w : ew.aa w.id with
  | none => simp [h_w, h_addr_l] at h_same
  | some aw =>
    simp [h_w, h_addr_l] at h_same
    rw [h_same]

/-- Helper lemma: an instruction cannot be both a load and a store -/
theorem load_not_store (i : Instruction) :
    i.isLoad = true → i.isStore = true → False := by
  intro h_load h_store
  unfold Instruction.isLoad Instruction.isStore at *
  cases h : i.instType <;> simp [h] at h_load h_store

end GamI2e
