/-
COM: SC-per-Location Relation Definition and Basic Lemmas

This module defines the SC-per-Location relation (rf ∪ co ∪ fr ∪ poloc)
and provides basic lemmas about edge types and relation properties.
-/

import GamI2e.COM.ECO.Base

namespace GamI2e

/-! ### SC-per-Location proof helpers -/

/-- rf is functional -/
theorem rf_functional (aa : AddressAssignment) (rf : ReadFrom aa) (s1 s2 l : Instruction) :
    rf.rel s1 l → rf.rel s2 l → s1 = s2 :=
  rf.functional l s1 s2

/-- rf;fr gives co -/
theorem rf_fr_gives_co (aa : AddressAssignment) (rf : ReadFrom aa) (mo : MemoryOrder)
    (s l s' : Instruction) (h_rf : rf.rel s l) (h_fr : fromReads aa rf mo l s') :
    coherenceOrderAll aa mo s s' := by
  unfold fromReads at h_fr
  obtain ⟨_, h_s'_store, w, h_w_rf, h_w_same, h_w_mo⟩ := h_fr
  have h_eq : s = w := rf.functional l s w h_rf h_w_rf
  subst h_eq
  have h_s_store := (rf.storeToLoad s l h_rf).1
  exact ⟨h_s_store, h_s'_store, h_w_same, h_w_mo⟩

/-- Helper: transgen of mo implies mo -/
theorem mo_transgen_to_mo (mo : MemoryOrder) (a b : Instruction)
    (h : Relation.TransGen mo.rel a b) : mo.rel a b := by
  induction h with
  | single h => exact h
  | tail _ h_last ih => exact mo.trans _ _ _ ih h_last

/-- co is acyclic (follows from mo being a strict order) -/
theorem co_acyclic_param (aa : AddressAssignment) (mo : MemoryOrder) :
    acyclic (coherenceOrderAll aa mo) := by
  intro i h_cycle
  have h_mo_trans : Relation.TransGen mo.rel i i := by
    have lift : ∀ a b, Relation.TransGen (coherenceOrderAll aa mo) a b → Relation.TransGen mo.rel a b := by
      intro a b h
      induction h with
      | single h_co => exact Relation.TransGen.single h_co.2.2.2
      | tail _ h_co ih => exact Relation.TransGen.tail ih h_co.2.2.2
    exact lift i i h_cycle
  exact mo.irrefl i (mo_transgen_to_mo mo i i h_mo_trans)

/-- rf source is a store -/
theorem rf_source_is_store (aa : AddressAssignment) (rf : ReadFrom aa) (s l : Instruction)
    (h : rf.rel s l) : s.isStore = true := (rf.storeToLoad s l h).1

/-- rf target is a load -/
theorem rf_target_is_load (aa : AddressAssignment) (rf : ReadFrom aa) (s l : Instruction)
    (h : rf.rel s l) : l.isLoad = true := (rf.storeToLoad s l h).2

/-- fr source is a load -/
theorem fr_source_is_load (aa : AddressAssignment) (rf : ReadFrom aa) (mo : MemoryOrder)
    (l s : Instruction) (h : fromReads aa rf mo l s) : l.isLoad = true := h.1

/-- fr target is a store -/
theorem fr_target_is_store (aa : AddressAssignment) (rf : ReadFrom aa) (mo : MemoryOrder)
    (l s : Instruction) (h : fromReads aa rf mo l s) : s.isStore = true := h.2.1

/-- co source is a store -/
theorem co_source_is_store (aa : AddressAssignment) (mo : MemoryOrder)
    (s1 s2 : Instruction) (h : coherenceOrderAll aa mo s1 s2) : s1.isStore = true := h.1

/-- co target is a store -/
theorem co_target_is_store (aa : AddressAssignment) (mo : MemoryOrder)
    (s1 s2 : Instruction) (h : coherenceOrderAll aa mo s1 s2) : s2.isStore = true := h.2.1

/-- Definition of sc_rel: rf ∪ co ∪ fr ∪ poloc -/
def sc_rel (ew : ExecutionWitness) : Relation :=
  let co := coherenceOrderAll ew.aa ew.mo
  let fr := fromReads ew.aa ew.rf ew.mo
  let poloc := programOrderLoc ew.aa ew.po
  unionRel (unionRel (unionRel ew.rf.rel co) fr) poloc

/-- SC-per-Location edge between two stores is exactly co -/
theorem sc_perloc_stores_is_co (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew)
    (s1 s2 : Instruction) (h_s1 : s1.isStore = true) (h_s2 : s2.isStore = true)
    (h_edge : ew.rf.rel s1 s2 ∨ coherenceOrderAll ew.aa ew.mo s1 s2 ∨
              fromReads ew.aa ew.rf ew.mo s1 s2 ∨ programOrderLoc ew.aa ew.po s1 s2) :
    coherenceOrderAll ew.aa ew.mo s1 s2 := by
  cases h_edge with
  | inl h_rf =>
    have h_s2_load := (ew.rf.storeToLoad s1 s2 h_rf).2
    exact absurd h_s2 (load_not_store s2 h_s2_load)
  | inr h_rest =>
    cases h_rest with
    | inl h_co => exact h_co
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_fr =>
        have h_s1_load := h_fr.1
        exact absurd h_s1 (load_not_store s1 h_s1_load)
      | inr h_poloc =>
        unfold programOrderLoc at h_poloc
        obtain ⟨h_po, h_same, _, _⟩ := h_poloc
        have h_pposa : preservedSameAddrOrder ew.aa ew.po s1 s2 := by
          right; left; exact ⟨h_s1, h_s2, h_po, h_same⟩
        have h_s1_mem := isStore_implies_isMemInst s1 h_s1
        have h_s2_mem := isStore_implies_isMemInst s2 h_s2
        have h_mo := h_instOrder s1 s2 (pposa_subset_ppo ew.aa of ew.po s1 s2 h_pposa) h_s1_mem h_s2_mem
        exact ⟨h_s1, h_s2, h_same, h_mo⟩

/-- poloc from load to store gives fr -/
theorem poloc_load_store_is_fr (of : OrderedFunc) (ew : ExecutionWitness)
    (h_loadValue : satisfies_LoadValue ew)
    (h_instOrder : satisfies_InstOrder of ew)
    (l s : Instruction) (h_l : l.isLoad = true) (h_s : s.isStore = true)
    (h_poloc : programOrderLoc ew.aa ew.po l s) :
    fromReads ew.aa ew.rf ew.mo l s := by
  have h_eco := eco_poloc of ew h_loadValue h_instOrder l s h_poloc
    (Or.inl h_l) (Or.inr h_s)
  unfold extendedCommunication at h_eco
  cases h_eco with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_co => exact absurd (co_source_is_store ew.aa ew.mo l s h_co) (load_not_store l h_l)
      | inr h_fr => exact h_fr
    | inr h_co_star_rf =>
      unfold composeRel reflTransClosure at h_co_star_rf
      obtain ⟨w, _, h_rf_w_s⟩ := h_co_star_rf
      exact absurd h_s (load_not_store s (rf_target_is_load ew.aa ew.rf w s h_rf_w_s))
  | inr h_rf_co_rf =>
    unfold composeRel inverseRel reflTransClosure at h_rf_co_rf
    obtain ⟨_, _, _, _, h_rf⟩ := h_rf_co_rf
    exact absurd h_s (load_not_store s (rf_target_is_load ew.aa ew.rf _ s h_rf))

/-- poloc from store to load gives co*;rf witness -/
theorem poloc_store_load_gives_rf (of : OrderedFunc) (ew : ExecutionWitness)
    (h_loadValue : satisfies_LoadValue ew)
    (h_instOrder : satisfies_InstOrder of ew)
    (s l : Instruction) (h_s : s.isStore = true) (h_l : l.isLoad = true)
    (h_poloc : programOrderLoc ew.aa ew.po s l) :
    ∃ w, (w = s ∨ Relation.TransGen (coherenceOrderAll ew.aa ew.mo) s w) ∧ ew.rf.rel w l := by
  have h_eco := eco_poloc of ew h_loadValue h_instOrder s l h_poloc (Or.inr h_s) (Or.inl h_l)
  unfold extendedCommunication at h_eco
  cases h_eco with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_co => exact absurd (co_target_is_store ew.aa ew.mo s l h_co) (load_not_store l h_l)
      | inr h_fr => exact absurd h_s (load_not_store s (fr_source_is_load ew.aa ew.rf ew.mo s l h_fr))
    | inr h_co_star_rf =>
      unfold composeRel reflTransClosure at h_co_star_rf
      obtain ⟨w, h_co_star, h_rf⟩ := h_co_star_rf
      cases h_co_star with
      | inl h_eq => exact ⟨w, Or.inl h_eq.symm, h_rf⟩
      | inr h_trans => exact ⟨w, Or.inr h_trans, h_rf⟩
  | inr h_rf_co_rf =>
    unfold composeRel inverseRel at h_rf_co_rf
    obtain ⟨w, h_rf_w_s, _⟩ := h_rf_co_rf
    exact absurd h_s (load_not_store s (rf_target_is_load ew.aa ew.rf w s h_rf_w_s))

/-- sc_rel edge types -/
inductive SCRelEdgeType (ew : ExecutionWitness) (i1 i2 : Instruction) : Prop where
  | rf_edge : ew.rf.rel i1 i2 → SCRelEdgeType ew i1 i2
  | co_edge : coherenceOrderAll ew.aa ew.mo i1 i2 → SCRelEdgeType ew i1 i2
  | fr_edge : fromReads ew.aa ew.rf ew.mo i1 i2 → SCRelEdgeType ew i1 i2
  | poloc_edge : programOrderLoc ew.aa ew.po i1 i2 → SCRelEdgeType ew i1 i2

/-- Convert sc_rel to edge type -/
theorem sc_rel_to_edge_type (ew : ExecutionWitness) (i1 i2 : Instruction)
    (h : sc_rel ew i1 i2) : SCRelEdgeType ew i1 i2 := by
  unfold sc_rel at h
  cases h with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf => exact SCRelEdgeType.rf_edge h_rf
      | inr h_co => exact SCRelEdgeType.co_edge h_co
    | inr h_fr => exact SCRelEdgeType.fr_edge h_fr
  | inr h_poloc => exact SCRelEdgeType.poloc_edge h_poloc

/-- sc_rel edge is contained in mo for store→store edges -/
theorem sc_rel_store_store_to_mo (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew)
    (s1 s2 : Instruction) (h_s1 : s1.isStore = true) (h_s2 : s2.isStore = true)
    (h_edge : sc_rel ew s1 s2) :
    ew.mo.rel s1 s2 := by
  unfold sc_rel unionRel at h_edge
  have h_or : ew.rf.rel s1 s2 ∨ coherenceOrderAll ew.aa ew.mo s1 s2 ∨
              fromReads ew.aa ew.rf ew.mo s1 s2 ∨ programOrderLoc ew.aa ew.po s1 s2 := by
    cases h_edge with
    | inl h123 =>
      cases h123 with
      | inl h12 =>
        cases h12 with
        | inl h_rf => exact Or.inl h_rf
        | inr h_co => exact Or.inr (Or.inl h_co)
      | inr h_fr => exact Or.inr (Or.inr (Or.inl h_fr))
    | inr h_poloc => exact Or.inr (Or.inr (Or.inr h_poloc))
  exact (sc_perloc_stores_is_co of ew h_instOrder s1 s2 h_s1 h_s2 h_or).2.2.2

/-- sc_rel edge INTO a load must be either rf or poloc -/
theorem sc_rel_edge_to_load (ew : ExecutionWitness)
    (i l : Instruction) (h_l : l.isLoad = true) (h_edge : sc_rel ew i l) :
    ew.rf.rel i l ∨ programOrderLoc ew.aa ew.po i l := by
  unfold sc_rel unionRel at h_edge
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf => exact Or.inl h_rf
      | inr h_co => exact absurd (co_target_is_store ew.aa ew.mo i l h_co) (load_not_store l h_l)
    | inr h_fr => exact absurd (fr_target_is_store ew.aa ew.rf ew.mo i l h_fr) (load_not_store l h_l)
  | inr h_poloc => exact Or.inr h_poloc

/-- sc_rel edge FROM a load must be either fr or poloc -/
theorem sc_rel_edge_from_load (ew : ExecutionWitness)
    (l i : Instruction) (h_l : l.isLoad = true) (h_edge : sc_rel ew l i) :
    fromReads ew.aa ew.rf ew.mo l i ∨ programOrderLoc ew.aa ew.po l i := by
  unfold sc_rel unionRel at h_edge
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf => exact absurd (rf_source_is_store ew.aa ew.rf l i h_rf) (load_not_store l h_l)
      | inr h_co => exact absurd (co_source_is_store ew.aa ew.mo l i h_co) (load_not_store l h_l)
    | inr h_fr => exact Or.inl h_fr
  | inr h_poloc => exact Or.inr h_poloc

/-- Edge from store to store in sc_rel gives mo -/
theorem sc_rel_store_to_store_gives_mo (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew)
    (s1 s2 : Instruction) (h_s1 : s1.isStore = true) (h_s2 : s2.isStore = true)
    (h_edge : sc_rel ew s1 s2) :
    ew.mo.rel s1 s2 := by
  have h_co := sc_perloc_stores_is_co of ew h_instOrder s1 s2 h_s1 h_s2
  unfold sc_rel unionRel at h_edge
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf =>
        have h_s2_load := rf_target_is_load ew.aa ew.rf s1 s2 h_rf
        exact absurd h_s2 (load_not_store s2 h_s2_load)
      | inr h_co => exact h_co.2.2.2
    | inr h_fr =>
      have h_s1_load := fr_source_is_load ew.aa ew.rf ew.mo s1 s2 h_fr
      exact absurd h_s1 (load_not_store s1 h_s1_load)
  | inr h_poloc =>
    have h_or : ew.rf.rel s1 s2 ∨ coherenceOrderAll ew.aa ew.mo s1 s2 ∨
                fromReads ew.aa ew.rf ew.mo s1 s2 ∨ programOrderLoc ew.aa ew.po s1 s2 :=
      Or.inr (Or.inr (Or.inr h_poloc))
    exact (h_co h_or).2.2.2

/-- Edge from store to load in sc_rel: either rf directly or poloc (which gives rf via eco) -/
theorem sc_rel_store_to_load_rf_or_poloc (ew : ExecutionWitness)
    (s l : Instruction) (_h_s : s.isStore = true) (h_l : l.isLoad = true)
    (h_edge : sc_rel ew s l) :
    ew.rf.rel s l ∨ programOrderLoc ew.aa ew.po s l := by
  unfold sc_rel unionRel at h_edge
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf => exact Or.inl h_rf
      | inr h_co => exact absurd (co_target_is_store ew.aa ew.mo s l h_co) (load_not_store l h_l)
    | inr h_fr => exact absurd (fr_target_is_store ew.aa ew.rf ew.mo s l h_fr) (load_not_store l h_l)
  | inr h_poloc => exact Or.inr h_poloc

/-- Edge from load to store in sc_rel: either fr directly or poloc (which gives fr via eco) -/
theorem sc_rel_load_to_store_fr_or_poloc (ew : ExecutionWitness)
    (l s : Instruction) (h_l : l.isLoad = true) (_h_s : s.isStore = true)
    (h_edge : sc_rel ew l s) :
    fromReads ew.aa ew.rf ew.mo l s ∨ programOrderLoc ew.aa ew.po l s := by
  unfold sc_rel unionRel at h_edge
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf => exact absurd (rf_source_is_store ew.aa ew.rf l s h_rf) (load_not_store l h_l)
      | inr h_co => exact absurd (co_source_is_store ew.aa ew.mo l s h_co) (load_not_store l h_l)
    | inr h_fr => exact Or.inl h_fr
  | inr h_poloc => exact Or.inr h_poloc

/-- Helper: contradiction for edges from non-memory instruction -/
theorem sc_rel_edge_from_non_mem_absurd (ew : ExecutionWitness)
    (mid next : Instruction) (h_edge : sc_rel ew mid next)
    (h_not_load : ¬mid.isLoad = true) (h_not_store : ¬mid.isStore = true) : False := by
  unfold sc_rel unionRel at h_edge
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf => exact absurd (rf_source_is_store ew.aa ew.rf mid next h_rf) h_not_store
      | inr h_co => exact absurd (co_source_is_store ew.aa ew.mo mid next h_co) h_not_store
    | inr h_fr_edge => exact absurd (fr_source_is_load ew.aa ew.rf ew.mo mid next h_fr_edge) h_not_load
  | inr h_poloc_edge =>
    have h_mid_mem := h_poloc_edge.2.2.1
    rw [isMemInst_iff_load_or_store] at h_mid_mem
    cases h_mid_mem with
    | inl h => exact absurd h h_not_load
    | inr h => exact absurd h h_not_store

/-- Extract poloc from sc_rel edge between loads -/
theorem sc_rel_load_load_is_poloc (ew : ExecutionWitness)
    (l1 l2 : Instruction) (h_l1 : l1.isLoad = true) (h_l2 : l2.isLoad = true)
    (h_edge : sc_rel ew l1 l2) : programOrderLoc ew.aa ew.po l1 l2 := by
  unfold sc_rel unionRel at h_edge
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rf => exact absurd (rf_source_is_store ew.aa ew.rf l1 l2 h_rf) (load_not_store l1 h_l1)
      | inr h_co => exact absurd (co_source_is_store ew.aa ew.mo l1 l2 h_co) (load_not_store l1 h_l1)
    | inr h_fr => exact absurd (fr_target_is_store ew.aa ew.rf ew.mo l1 l2 h_fr) (load_not_store l2 h_l2)
  | inr h_poloc => exact h_poloc

/-- Helper to get address from rf source -/
theorem rf_source_has_addr (ew : ExecutionWitness) (w l : Instruction)
    (h_rf : ew.rf.rel w l) (h_l_has_addr : (ew.aa l.id).isSome) : (ew.aa w.id).isSome := by
  have h := ew.rf.sameAddr w l h_rf
  simp [Instruction.sameAddrWith] at h
  cases h_l_addr : ew.aa l.id with
  | none => simp [h_l_addr] at h_l_has_addr
  | some a =>
    cases h_w_addr : ew.aa w.id with
    | none => simp [h_w_addr, h_l_addr] at h
    | some _ => rfl

end GamI2e
