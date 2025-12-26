/-
COM: Causality Helper Lemmas

This module contains utility lemmas used in proving the Causality axiom,
including lemmas about relations being contained in mo, TransGen utilities,
and properties of rfe/co/fr relating to memory instructions.
-/

import GamI2e.COM.Definitions

namespace GamI2e

/-- Helper lemma: if w rf l, then either w po l or w mo l -/
theorem rf_implies_po_or_mo (ew : ExecutionWitness) :
    satisfies_LoadValue ew →
    ∀ w l, ew.rf.rel w l → (ew.po.rel w l ∨ ew.mo.rel w l) := by
  intro h_loadValue w l h_rf
  -- By ReadFrom properties, w is a store and l is a load at same address
  have h_w_store_l_load := ew.rf.storeToLoad w l h_rf
  have h_w_store := h_w_store_l_load.1
  have h_l_load := h_w_store_l_load.2
  have h_same := ew.rf.sameAddr w l h_rf
  -- sameAddrWith means both have addresses and they're equal
  simp [Instruction.sameAddrWith] at h_same
  -- We need to extract the actual address
  cases h_w_addr : ew.aa w.id with
  | none =>
    simp [h_w_addr] at h_same
  | some a =>
    cases h_l_addr : ew.aa l.id with
    | none =>
      simp [h_w_addr, h_l_addr] at h_same
    | some a' =>
      -- Apply Load-Value axiom to get visibility property
      have h_visibility_and_maximal := loadValue_iff ew w l a h_loadValue h_rf h_w_store h_l_load h_w_addr
      simp [h_w_addr, h_l_addr] at h_same
      have h_a_eq : a = a' := by
        cases h_same
        rfl
      subst h_a_eq
      exact (h_visibility_and_maximal h_l_addr).1

/-- Key lemma for GAM ⊆ COM: all COM relations between memory instructions are contained in mo.

    Note: The PPO case requires explicit memory instruction hypotheses because PPO
    can contain fences (via ppomf) and branches (via ppod case 2). However, in the
    context of COM acyclicity proofs, edges in cycles involving rf/co/fr must connect
    to memory instructions at the interface points.

    For rf, co, and fr, we can derive that the endpoints are memory instructions
    from the relation definitions. For ppo, this must be established from context. -/
theorem com_contained_in_mo (of : OrderedFunc) (ew : ExecutionWitness) :
    satisfies_InstOrder of ew →
    satisfies_LoadValue ew →
    (∀ i1 i2,
      i1.isMemInst →
      i2.isMemInst →
      (readFromExternal ew.aa ew.rf i1 i2 ∨
       coherenceOrderAll ew.aa ew.mo i1 i2 ∨
       fromReads ew.aa ew.rf ew.mo i1 i2 ∨
       preservedProgramOrder ew.aa of ew.po i1 i2) →
      ew.mo.rel i1 i2) := by
  intro h_instOrder h_loadValue i1 i2 h_i1_mem h_i2_mem h_com
  cases h_com with
  | inl h_rfe =>
    -- rfe case: rf with different processors implies mo by Load-Value
    unfold readFromExternal at h_rfe
    have h_po_or_mo := rf_implies_po_or_mo ew h_loadValue i1 i2 h_rfe.1
    cases h_po_or_mo with
    | inl h_po => exact absurd (ew.po.sameProc i1 i2 h_po) h_rfe.2
    | inr h_mo => exact h_mo
  | inr h_rest =>
    cases h_rest with
    | inl h_co =>
      -- co case: coherence order is mo restricted to same-address stores
      unfold coherenceOrderAll at h_co
      exact h_co.2.2.2
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_fr =>
        -- fr case: from-reads implies mo by Load-Value maximality
        unfold fromReads at h_fr
        obtain ⟨h_i1_load, h_i2_store, w', h_rf_w'_i1, h_same_w'_i2, h_mo_w'_i2⟩ := h_fr
        have h_neq : i1 ≠ i2 := fun h_eq => load_not_store i1 h_i1_load (h_eq ▸ h_i2_store)
        cases ew.mo.total i1 i2 h_i1_mem h_i2_mem h_neq with
        | inl h_i1_mo_i2 => exact h_i1_mo_i2
        | inr h_i2_mo_i1 =>
          exfalso
          have ⟨h_w'_store, h_i1_load'⟩ := ew.rf.storeToLoad w' i1 h_rf_w'_i1
          have h_same_w'_i1 := ew.rf.sameAddr w' i1 h_rf_w'_i1
          simp [Instruction.sameAddrWith] at h_same_w'_i1 h_same_w'_i2
          cases h_w'_addr : ew.aa w'.id with
          | none => simp [h_w'_addr] at h_same_w'_i1
          | some a =>
            cases h_i1_addr : ew.aa i1.id with
            | none => simp [h_w'_addr, h_i1_addr] at h_same_w'_i1
            | some a1 =>
              cases h_i2_addr : ew.aa i2.id with
              | none => simp [h_w'_addr, h_i2_addr] at h_same_w'_i2
              | some a2 =>
                simp [h_w'_addr, h_i1_addr, h_i2_addr] at h_same_w'_i1 h_same_w'_i2
                cases h_same_w'_i1; cases h_same_w'_i2
                have h_w'_maximal := (loadValue_iff ew w' i1 a h_loadValue h_rf_w'_i1 h_w'_store h_i1_load' h_w'_addr h_i1_addr).2
                have h_i2_before_w' := h_w'_maximal i2 h_i2_store h_i2_addr (Or.inr h_i2_mo_i1)
                cases h_i2_before_w' with
                | inl h_i2_mo_w' => exact ew.mo.irrefl w' (ew.mo.trans w' i2 w' h_mo_w'_i2 h_i2_mo_w')
                | inr h_i2_eq_w' => exact ew.mo.irrefl w' (h_i2_eq_w' ▸ h_mo_w'_i2)
      | inr h_ppo =>
        -- ppo case: preserved program order implies mo by Inst-Order
        exact h_instOrder i1 i2 h_ppo h_i1_mem h_i2_mem

/-- Helper: lifting through TransGen (local copy) -/
theorem transGen_lift' {α : Type _} (r1 r2 : α → α → Prop)
    (h : ∀ x y, r1 x y → r2 x y) :
    ∀ x y, Relation.TransGen r1 x y → Relation.TransGen r2 x y := by
  intro x y h_trans
  induction h_trans with
  | single h_edge =>
    exact Relation.TransGen.single (h _ _ h_edge)
  | tail h_rest h_last ih =>
    exact Relation.TransGen.tail ih (h _ _ h_last)

/-- Key lemma: If all edges in a path from a non-mem node are ppo edges,
    then the path gives ppo by transitivity.

    Note: ppo is defined as TransGen of the base relation, so TransGen ppo
    collapses to ppo via transitivity. -/
theorem transGen_ppo_is_ppo (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) :
    ∀ a b, Relation.TransGen (preservedProgramOrder aa of po) a b →
    preservedProgramOrder aa of po a b := by
  intro a b h
  -- TransGen (TransGen r) collapses to TransGen r
  induction h with
  | single h_ppo => exact h_ppo
  | tail _ h_last ih => exact Relation.TransGen.trans ih h_last

/-- Helper: extract the first edge from a TransGen path.
    If TransGen r a b, then there exists c such that r a c and either c = b or TransGen r c b. -/
theorem transGen_first_edge {α : Sort u} {r : α → α → Prop} (a b : α)
    (h : Relation.TransGen r a b) :
    ∃ c, r a c ∧ (c = b ∨ Relation.TransGen r c b) := by
  induction h with
  | single h_edge =>
    exact ⟨_, h_edge, Or.inl rfl⟩
  | tail h_trans h_last ih =>
    obtain ⟨c, h_first, h_rest⟩ := ih
    cases h_rest with
    | inl h_eq =>
      subst h_eq
      exact ⟨c, h_first, Or.inr (Relation.TransGen.single h_last)⟩
    | inr h_trans_cy =>
      exact ⟨c, h_first, Or.inr (Relation.TransGen.tail h_trans_cy h_last)⟩

/-- rf is contained in eco (via co*;rf component where co* = identity) -/
theorem rf_subset_eco (ew : ExecutionWitness) :
    ∀ s l, ew.rf.rel s l → extendedCommunication ew s l := by
  intro s l h_rf
  unfold extendedCommunication
  -- rf ⊆ co*;rf, where co* includes identity via reflTransClosure
  left; right  -- Choose co*;rf branch
  unfold composeRel reflTransClosure
  exact ⟨s, Or.inl rfl, h_rf⟩

/-- co is contained in eco (directly) -/
theorem co_subset_eco (ew : ExecutionWitness) :
    ∀ i1 i2, coherenceOrderAll ew.aa ew.mo i1 i2 → extendedCommunication ew i1 i2 := by
  intro i1 i2 h_co
  unfold extendedCommunication
  left; left; left  -- Choose co branch
  exact h_co

/-- fr is contained in eco (directly) -/
theorem fr_subset_eco (ew : ExecutionWitness) :
    ∀ i1 i2, fromReads ew.aa ew.rf ew.mo i1 i2 → extendedCommunication ew i1 i2 := by
  intro i1 i2 h_fr
  unfold extendedCommunication
  left; left; right  -- Choose fr branch
  exact h_fr

/-- Helper: rf ∪ co ∪ fr is contained in eco -/
theorem rf_co_fr_subset_eco (ew : ExecutionWitness) :
    ∀ i1 i2, (ew.rf.rel i1 i2 ∨ coherenceOrderAll ew.aa ew.mo i1 i2 ∨
              fromReads ew.aa ew.rf ew.mo i1 i2) →
    extendedCommunication ew i1 i2 := by
  intro i1 i2 h
  cases h with
  | inl h_rf => exact rf_subset_eco ew i1 i2 h_rf
  | inr h_rest =>
    cases h_rest with
    | inl h_co => exact co_subset_eco ew i1 i2 h_co
    | inr h_fr => exact fr_subset_eco ew i1 i2 h_fr

/-! ### Note on eco irreflexivity

eco is NOT irreflexive with the paper's definition using co*.
Specifically, rf⁻¹;co*;rf relates any load to itself (via the empty co* path).
This is fine - the paper's proof doesn't require eco irreflexivity.

The old eco_irrefl theorem (removed) required co+ in the last component.
With the paper's co* definition, we use a different proof strategy for
SC-per-Location that doesn't rely on eco acyclicity. -/

/-- Helper: if a relation is contained in an acyclic relation, it is acyclic -/
theorem acyclic_of_subset {r1 r2 : Relation}
    (h_sub : ∀ i1 i2, r1 i1 i2 → r2 i1 i2)
    (h_acyc : acyclic r2) : acyclic r1 := by
  intro i h_cycle
  -- Lift the cycle through the subset relation
  apply h_acyc i
  exact transGen_lift' r1 r2 h_sub i i h_cycle

/-- co is acyclic (since co ⊆ mo and mo is acyclic) -/
theorem co_acyclic (ew : ExecutionWitness) : acyclic (coherenceOrderAll ew.aa ew.mo) := by
  apply acyclic_of_subset
  · intro i1 i2 h_co
    unfold coherenceOrderAll at h_co
    exact h_co.2.2.2
  · exact mo_acyclic ew

/-- rf;fr is contained in co.
    If s rf l and l fr w, then s co w.
    Proof: l fr w means l reads from some s' with s' mo w (and same address).
    By rf.functional, s = s'. So s mo w, and we need s co w. -/
theorem rf_fr_subset_co (ew : ExecutionWitness) :
    ∀ s l w, ew.rf.rel s l → fromReads ew.aa ew.rf ew.mo l w → coherenceOrderAll ew.aa ew.mo s w := by
  intro s l w h_rf h_fr
  unfold fromReads at h_fr
  obtain ⟨h_l_load, h_w_store, s', h_s'_rf_l, h_same_s'_w, h_mo_s'_w⟩ := h_fr
  -- By rf.functional: s = s'
  have h_s_eq_s' := ew.rf.functional l s s' h_rf h_s'_rf_l
  subst h_s_eq_s'
  -- Now we have: s rf l, s mo w, w is a store, s sameAddrWith w
  -- Need: coherenceOrderAll = s.isStore ∧ w.isStore ∧ sameAddrWith ∧ mo
  have h_s_store := (ew.rf.storeToLoad s l h_rf).1
  exact ⟨h_s_store, h_w_store, h_same_s'_w, h_mo_s'_w⟩

/-- Helper: if r is transitive, TransGen r = r (transitivity collapses the transitive closure) -/
private theorem transGen_of_trans {r : Relation}
    (h_trans : ∀ i j k, r i j → r j k → r i k) :
    ∀ a b, Relation.TransGen r a b → r a b := by
  intro a b h
  induction h with
  | single h_edge => exact h_edge
  | tail h_rest h_last ih =>
    -- ih : r a b✝, h_last : r b✝ b
    exact h_trans _ _ _ ih h_last

/-- Helper: if r is both irreflexive and transitive (a strict partial order), it's acyclic.

    **NOTE:** The weaker theorem "irrefl → acyclic" is FALSE!
    Counterexample: r = {(0,1), (1,0)} is irreflexive but has cycle 0→1→0.

    This version requires transitivity, allowing us to collapse TransGen r i i to r i i. -/
theorem acyclic_of_strict_order {r : Relation}
    (h_irrefl : ∀ i, ¬r i i)
    (h_trans : ∀ i j k, r i j → r j k → r i k) : acyclic r := by
  intro i h_cycle
  -- Use transitivity to collapse TransGen to a single step
  have h_rii : r i i := transGen_of_trans h_trans i i h_cycle
  exact h_irrefl i h_rii

/-- Helper: four-way union of relations contained in mo is acyclic -/
theorem union4_acyclic_of_mo (ew : ExecutionWitness)
    (r1 r2 r3 r4 : Relation)
    (h_r1 : ∀ i1 i2, r1 i1 i2 → ew.mo.rel i1 i2)
    (h_r2 : ∀ i1 i2, r2 i1 i2 → ew.mo.rel i1 i2)
    (h_r3 : ∀ i1 i2, r3 i1 i2 → ew.mo.rel i1 i2)
    (h_r4 : ∀ i1 i2, r4 i1 i2 → ew.mo.rel i1 i2) :
    acyclic (unionRel (unionRel (unionRel r1 r2) r3) r4) := by
  apply acyclic_of_subset
  · intro i1 i2 h_union
    cases h_union with
    | inl h123 =>
      cases h123 with
      | inl h12 =>
        cases h12 with
        | inl h1 => exact h_r1 i1 i2 h1
        | inr h2 => exact h_r2 i1 i2 h2
      | inr h3 => exact h_r3 i1 i2 h3
    | inr h4 => exact h_r4 i1 i2 h4
  · exact mo_acyclic ew

/-- rfe requires both endpoints to be memory instructions -/
theorem rfe_mem_source (ew : ExecutionWitness) (i1 i2 : Instruction) :
    readFromExternal ew.aa ew.rf i1 i2 → i1.isMemInst = true := by
  intro h_rfe
  unfold readFromExternal at h_rfe
  exact isStore_implies_isMemInst i1 (ew.rf.storeToLoad i1 i2 h_rfe.1).1

theorem rfe_mem_target (ew : ExecutionWitness) (i1 i2 : Instruction) :
    readFromExternal ew.aa ew.rf i1 i2 → i2.isMemInst = true := by
  intro h_rfe
  unfold readFromExternal at h_rfe
  exact isLoad_implies_isMemInst i2 (ew.rf.storeToLoad i1 i2 h_rfe.1).2

/-- co requires both endpoints to be memory instructions (stores) -/
theorem co_mem_source (ew : ExecutionWitness) (i1 i2 : Instruction) :
    coherenceOrderAll ew.aa ew.mo i1 i2 → i1.isMemInst = true := by
  intro h_co
  unfold coherenceOrderAll at h_co
  exact isStore_implies_isMemInst i1 h_co.1

theorem co_mem_target (ew : ExecutionWitness) (i1 i2 : Instruction) :
    coherenceOrderAll ew.aa ew.mo i1 i2 → i2.isMemInst = true := by
  intro h_co
  unfold coherenceOrderAll at h_co
  exact isStore_implies_isMemInst i2 h_co.2.1

/-- fr requires both endpoints to be memory instructions -/
theorem fr_mem_source (ew : ExecutionWitness) (i1 i2 : Instruction) :
    fromReads ew.aa ew.rf ew.mo i1 i2 → i1.isMemInst = true := by
  intro h_fr
  unfold fromReads at h_fr
  exact isLoad_implies_isMemInst i1 h_fr.1

theorem fr_mem_target (ew : ExecutionWitness) (i1 i2 : Instruction) :
    fromReads ew.aa ew.rf ew.mo i1 i2 → i2.isMemInst = true := by
  intro h_fr
  unfold fromReads at h_fr
  exact isStore_implies_isMemInst i2 h_fr.2.1

end GamI2e
