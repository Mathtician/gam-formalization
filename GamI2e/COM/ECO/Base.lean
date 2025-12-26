/-
COM: Extended Communication Order (ECO) Base Lemmas

This module contains the fundamental ECO lemmas:
- eco_total_per_address: ECO is total over same-address accesses
- eco_poloc: Program order at same location implies ECO
- Various pposa (preserved same-address order) helpers
-/

import GamI2e.COM.Definitions

namespace GamI2e

/-- Helper: handle store-load case for eco_total -/
private theorem eco_total_store_load (ew : ExecutionWitness)
    (s l : Instruction) (a : Addr)
    (h_s_store : s.isStore = true) (h_l_load : l.isLoad = true)
    (h_addr_s : ew.aa s.id = some a) (h_addr_l : ew.aa l.id = some a)
    (h_l_has_addr : (ew.aa l.id).isSome) :
    extendedCommunication ew s l ∨ extendedCommunication ew l s := by
  unfold extendedCommunication
  obtain ⟨w, h_rf⟩ := ew.rf.coverage l h_l_load h_l_has_addr
  have h_w_store := (ew.rf.storeToLoad w l h_rf).1
  have h_w_addr := rf_same_addr ew w l a h_rf h_addr_l
  by_cases h_eq : s = w
  · subst h_eq; left; left; right; unfold composeRel reflTransClosure; exact ⟨s, Or.inl rfl, h_rf⟩
  · have h_s_mem := isStore_implies_isMemInst s h_s_store
    have h_w_mem := isStore_implies_isMemInst w h_w_store
    cases ew.mo.total s w h_s_mem h_w_mem h_eq with
    | inl h_mo =>
      left; left; right; unfold composeRel reflTransClosure
      exact ⟨w, Or.inr (Relation.TransGen.single ⟨h_s_store, h_w_store,
        by simp [Instruction.sameAddrWith, h_addr_s, h_w_addr], h_mo⟩), h_rf⟩
    | inr h_mo =>
      right; left; left; right; unfold fromReads
      exact ⟨h_l_load, h_s_store, w, h_rf, by simp [Instruction.sameAddrWith, h_w_addr, h_addr_s], h_mo⟩

/-- Key lemma: eco is a total order over same-address accesses -/
theorem eco_total_per_address (ew : ExecutionWitness) (insts : List Instruction)
    (h_wf : ew.aa.onlyMemInst insts) (a : Addr) :
    ∀ i1 i2 : Instruction,
    i1 ∈ insts →
    i2 ∈ insts →
    (ew.aa i1.id = some a) →
    (ew.aa i2.id = some a) →
    i1 ≠ i2 →
    extendedCommunication ew i1 i2 ∨ extendedCommunication ew i2 i1 := by
  intro i1 i2 h_i1_mem h_i2_mem h_addr1 h_addr2 h_neq
  have h_i1_has_addr : (ew.aa i1.id).isSome := by simp [h_addr1]
  have h_i2_has_addr : (ew.aa i2.id).isSome := by simp [h_addr2]
  cases hasAddr_implies_load_or_store ew.aa insts h_wf i1 h_i1_mem h_i1_has_addr with
  | inl h_i1_load =>
    cases hasAddr_implies_load_or_store ew.aa insts h_wf i2 h_i2_mem h_i2_has_addr with
    | inl h_i2_load =>
      obtain ⟨w1, h_w1_rf⟩ := ew.rf.coverage i1 h_i1_load h_i1_has_addr
      obtain ⟨w2, h_w2_rf⟩ := ew.rf.coverage i2 h_i2_load h_i2_has_addr
      have h_w1_store := (ew.rf.storeToLoad w1 i1 h_w1_rf).1
      have h_w2_store := (ew.rf.storeToLoad w2 i2 h_w2_rf).1
      have h_w1_addr := rf_same_addr ew w1 i1 a h_w1_rf h_addr1
      have h_w2_addr := rf_same_addr ew w2 i2 a h_w2_rf h_addr2
      unfold extendedCommunication
      by_cases h_eq : w1 = w2
      · subst h_eq; left; right; unfold composeRel inverseRel reflTransClosure
        exact ⟨w1, h_w1_rf, w1, Or.inl rfl, h_w2_rf⟩
      · have h_w1_mem := isStore_implies_isMemInst w1 h_w1_store
        have h_w2_mem := isStore_implies_isMemInst w2 h_w2_store
        cases ew.mo.total w1 w2 h_w1_mem h_w2_mem h_eq with
        | inl h_mo =>
          left; right; unfold composeRel inverseRel reflTransClosure
          exact ⟨w1, h_w1_rf, w2, Or.inr (Relation.TransGen.single
            ⟨h_w1_store, h_w2_store, by simp [Instruction.sameAddrWith, h_w1_addr, h_w2_addr], h_mo⟩), h_w2_rf⟩
        | inr h_mo =>
          right; right; unfold composeRel inverseRel reflTransClosure
          exact ⟨w2, h_w2_rf, w1, Or.inr (Relation.TransGen.single
            ⟨h_w2_store, h_w1_store, by simp [Instruction.sameAddrWith, h_w2_addr, h_w1_addr], h_mo⟩), h_w1_rf⟩
    | inr h_i2_store =>
      cases eco_total_store_load ew i2 i1 a h_i2_store h_i1_load h_addr2 h_addr1 h_i1_has_addr with
      | inl h => right; exact h
      | inr h => left; exact h
  | inr h_i1_store =>
    cases hasAddr_implies_load_or_store ew.aa insts h_wf i2 h_i2_mem h_i2_has_addr with
    | inl h_i2_load => exact eco_total_store_load ew i1 i2 a h_i1_store h_i2_load h_addr1 h_addr2 h_i2_has_addr
    | inr h_i2_store =>
      unfold extendedCommunication
      have h_i1_mem := isStore_implies_isMemInst i1 h_i1_store
      have h_i2_mem := isStore_implies_isMemInst i2 h_i2_store
      cases ew.mo.total i1 i2 h_i1_mem h_i2_mem h_neq with
      | inl h_mo =>
        left; left; left; left
        exact ⟨h_i1_store, h_i2_store, by simp [Instruction.sameAddrWith, h_addr1, h_addr2], h_mo⟩
      | inr h_mo =>
        right; left; left; left
        exact ⟨h_i2_store, h_i1_store, by simp [Instruction.sameAddrWith, h_addr2, h_addr1], h_mo⟩

/-- Helper: derive mo from pposa via InstOrder -/
private theorem pposa_to_mo (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew)
    (i1 i2 : Instruction) (h_pposa : preservedSameAddrOrder ew.aa ew.po i1 i2)
    (h_i1_mem : i1.isMemInst) (h_i2_mem : i2.isMemInst) :
    ew.mo.rel i1 i2 :=
  h_instOrder i1 i2 (pposa_subset_ppo ew.aa of ew.po i1 i2 h_pposa) h_i1_mem h_i2_mem

/-- Helper: build pposa for load-store at same address -/
private theorem pposa_ld_st (aa : AddressAssignment) (po : ProgramOrder)
    (i1 i2 : Instruction) (a : Addr)
    (h_i1_load : i1.isLoad = true) (h_i2_store : i2.isStore = true)
    (h_po : po.rel i1 i2) (h_addr1 : aa i1.id = some a) (h_addr2 : aa i2.id = some a) :
    preservedSameAddrOrder aa po i1 i2 := by
  left; exact ⟨h_i1_load, h_i2_store, h_po, by simp [Instruction.sameAddrWith, h_addr1, h_addr2]⟩

/-- Helper: build pposa for store-store at same address -/
private theorem pposa_st_st (aa : AddressAssignment) (po : ProgramOrder)
    (i1 i2 : Instruction) (a : Addr)
    (h_i1_store : i1.isStore = true) (h_i2_store : i2.isStore = true)
    (h_po : po.rel i1 i2) (h_addr1 : aa i1.id = some a) (h_addr2 : aa i2.id = some a) :
    preservedSameAddrOrder aa po i1 i2 := by
  right; left; exact ⟨h_i1_store, h_i2_store, h_po, by simp [Instruction.sameAddrWith, h_addr1, h_addr2]⟩

/-- Helper: build pposa for load-load at same address without intervening store -/
private theorem pposa_ld_ld (aa : AddressAssignment) (po : ProgramOrder)
    (i1 i2 : Instruction) (a : Addr)
    (h_i1_load : i1.isLoad = true) (h_i2_load : i2.isLoad = true)
    (h_po : po.rel i1 i2) (h_addr1 : aa i1.id = some a) (h_addr2 : aa i2.id = some a)
    (h_no_int : ¬∃ s, s.isStore = true ∧ s.sameAddrWith aa i1 ∧ po.rel i1 s ∧ po.rel s i2) :
    preservedSameAddrOrder aa po i1 i2 := by
  right; right; exact ⟨h_i1_load, h_i2_load, h_po, by simp [Instruction.sameAddrWith, h_addr1, h_addr2], h_no_int⟩

/-- Helper: build co*;rf path for eco -/
private theorem eco_co_star_rf (ew : ExecutionWitness) (s1 s2 l : Instruction)
    (h_s1_store : s1.isStore = true) (h_s2_store : s2.isStore = true)
    (h_s1_mo_s2 : ew.mo.rel s1 s2) (h_rf : ew.rf.rel s2 l)
    (h_same : s1.sameAddrWith ew.aa s2) :
    extendedCommunication ew s1 l := by
  left; right; unfold composeRel reflTransClosure
  exact ⟨s2, Or.inr (Relation.TransGen.single ⟨h_s1_store, h_s2_store, h_same, h_s1_mo_s2⟩), h_rf⟩

/-- Helper: build fr path for eco -/
private theorem eco_fr (ew : ExecutionWitness) (l s w : Instruction)
    (h_l_load : l.isLoad = true) (h_s_store : s.isStore = true)
    (h_rf : ew.rf.rel w l) (h_w_mo_s : ew.mo.rel w s)
    (h_same : w.sameAddrWith ew.aa s) :
    extendedCommunication ew l s := by
  left; left; right; unfold fromReads
  exact ⟨h_l_load, h_s_store, w, h_rf, h_same, h_w_mo_s⟩

/-- poloc implies eco (Lemma 4). Proof by contradiction. -/
theorem eco_poloc (of : OrderedFunc) (ew : ExecutionWitness)
    (h_loadValue : satisfies_LoadValue ew)
    (h_instOrder : satisfies_InstOrder of ew) :
    ∀ i1 i2,
    programOrderLoc ew.aa ew.po i1 i2 →
    (i1.isLoad = true ∨ i1.isStore = true) →
    (i2.isLoad = true ∨ i2.isStore = true) →
    extendedCommunication ew i1 i2 := by
  intro i1 i2 h_poloc h_i1_mem h_i2_mem
  unfold programOrderLoc at h_poloc
  obtain ⟨h_po, h_same, _, _⟩ := h_poloc
  unfold extendedCommunication
  simp [Instruction.sameAddrWith] at h_same
  cases h_addr1 : ew.aa i1.id with | none => simp [h_addr1] at h_same | some a =>
  cases h_addr2 : ew.aa i2.id with | none => simp [h_addr1, h_addr2] at h_same | some a2 =>
  simp [h_addr1, h_addr2] at h_same
  have h_a_eq : a = a2 := h_same
  subst h_a_eq
  cases h_i1_mem with
  | inl h_i1_load => cases h_i2_mem with
    | inl h_i2_load =>
      obtain ⟨w1, h_w1_rf⟩ := ew.rf.coverage i1 h_i1_load (by simp [h_addr1] : (ew.aa i1.id).isSome)
      obtain ⟨w2, h_w2_rf⟩ := ew.rf.coverage i2 h_i2_load (by simp [h_addr2] : (ew.aa i2.id).isSome)
      have h_w1_store := (ew.rf.storeToLoad w1 i1 h_w1_rf).1
      have h_w2_store := (ew.rf.storeToLoad w2 i2 h_w2_rf).1
      have h_w1_addr := rf_same_addr ew w1 i1 a h_w1_rf h_addr1
      have h_w2_addr := rf_same_addr ew w2 i2 a h_w2_rf h_addr2
      by_cases h_eq : w1 = w2
      · subst h_eq
        right; unfold composeRel inverseRel reflTransClosure
        exact ⟨w1, h_w1_rf, w1, Or.inl rfl, h_w2_rf⟩
      · have h_w1_mem := isStore_implies_isMemInst w1 h_w1_store
        have h_w2_mem := isStore_implies_isMemInst w2 h_w2_store
        cases ew.mo.total w1 w2 h_w1_mem h_w2_mem h_eq with
        | inl h_mo =>
          right; unfold composeRel inverseRel reflTransClosure
          exact ⟨w1, h_w1_rf, w2, Or.inr (Relation.TransGen.single
            ⟨h_w1_store, h_w2_store, by simp [Instruction.sameAddrWith, h_w1_addr, h_w2_addr], h_mo⟩), h_w2_rf⟩
        | inr h_w2_mo_w1 =>
          exfalso
          have h_vis_w1 := h_loadValue w1 i1 a h_w1_addr h_addr1 h_w1_store h_i1_load h_w1_rf
          cases h_vis_w1.1 with
          | inl h_po_w1_i1 =>
            have h_vis_w2 := h_loadValue w2 i2 a h_w2_addr h_addr2 h_w2_store h_i2_load h_w2_rf
            cases h_vis_w2.2 w1 h_w1_store h_w1_addr (Or.inl (ew.po.trans w1 i1 i2 h_po_w1_i1 h_po)) with
            | inl h_mo => exact ew.mo.irrefl w2 (ew.mo.trans w2 w1 w2 h_w2_mo_w1 h_mo)
            | inr h_eq' => exact h_eq h_eq'
          | inr h_mo_w1_i1 =>
            by_cases h_int : ∃ s, s.isStore = true ∧ s.sameAddrWith ew.aa i1 ∧
                                   ew.po.rel i1 s ∧ ew.po.rel s i2
            · obtain ⟨s, h_s_st, h_s_same, h_po_i1_s, h_po_s_i2⟩ := h_int
              have h_s_addr : ew.aa s.id = some a := by
                simp [Instruction.sameAddrWith] at h_s_same
                cases h_s_id : ew.aa s.id with
                | none => simp [h_s_id, h_addr1] at h_s_same
                | some as => simp [h_s_id, h_addr1] at h_s_same; cases h_s_same; rfl
              have h_vis_w2 := h_loadValue w2 i2 a h_w2_addr h_addr2 h_w2_store h_i2_load h_w2_rf
              have h_s_mem := isStore_implies_isMemInst s h_s_st
              have h_i1_mem' := isLoad_implies_isMemInst i1 h_i1_load
              have h_i1_mo_s := pposa_to_mo of ew h_instOrder i1 s
                (pposa_ld_st ew.aa ew.po i1 s a h_i1_load h_s_st h_po_i1_s h_addr1 h_s_addr) h_i1_mem' h_s_mem
              have h_neq : i1 ≠ s := by
                intro h_eq; rw [h_eq] at h_i1_load
                simp only [Instruction.isLoad, Instruction.isStore] at h_i1_load h_s_st
                cases h : s.instType <;> simp [h] at h_i1_load h_s_st
              cases ew.mo.total s i1 h_s_mem h_i1_mem' (Ne.symm h_neq) with
              | inl h_mo => exact ew.mo.irrefl s (ew.mo.trans s i1 s h_mo h_i1_mo_s)
              | inr _ =>
                cases h_vis_w2.2 s h_s_st h_s_addr (Or.inl h_po_s_i2) with
                | inl h_mo =>
                  exact ew.mo.irrefl i1 (ew.mo.trans i1 w1 i1
                    (ew.mo.trans i1 w2 w1 (ew.mo.trans i1 s w2 h_i1_mo_s h_mo) h_w2_mo_w1) h_mo_w1_i1)
                | inr h_eq' =>
                  exact ew.mo.irrefl i1 (ew.mo.trans i1 w1 i1
                    (ew.mo.trans i1 s w1 h_i1_mo_s (h_eq' ▸ h_w2_mo_w1)) h_mo_w1_i1)
            · have h_i1_mem' := isLoad_implies_isMemInst i1 h_i1_load
              have h_i2_mem' := isLoad_implies_isMemInst i2 h_i2_load
              have h_i1_mo_i2 := pposa_to_mo of ew h_instOrder i1 i2
                (pposa_ld_ld ew.aa ew.po i1 i2 a h_i1_load h_i2_load h_po h_addr1 h_addr2 h_int) h_i1_mem' h_i2_mem'
              have h_vis_w2 := h_loadValue w2 i2 a h_w2_addr h_addr2 h_w2_store h_i2_load h_w2_rf
              cases h_vis_w2.2 w1 h_w1_store h_w1_addr (Or.inr (ew.mo.trans w1 i1 i2 h_mo_w1_i1 h_i1_mo_i2)) with
              | inl h_mo => exact ew.mo.irrefl w2 (ew.mo.trans w2 w1 w2 h_w2_mo_w1 h_mo)
              | inr h_eq' => exact h_eq h_eq'
    | inr h_i2_store =>
      obtain ⟨w, h_rf⟩ := ew.rf.coverage i1 h_i1_load (by simp [h_addr1] : (ew.aa i1.id).isSome)
      have h_w_store := (ew.rf.storeToLoad w i1 h_rf).1
      have h_w_addr := rf_same_addr ew w i1 a h_rf h_addr1
      by_cases h_eq : w = i2
      · exfalso
        have h_vis := h_loadValue w i1 a h_w_addr h_addr1 h_w_store h_i1_load h_rf
        rw [h_eq] at h_vis
        cases h_vis.1 with
        | inl h_po_i2_i1 => exact ew.po.irrefl i1 (ew.po.trans i1 i2 i1 h_po h_po_i2_i1)
        | inr h_mo_i2_i1 =>
          have h_i1_mem' := isLoad_implies_isMemInst i1 h_i1_load
          have h_i2_mem' := isStore_implies_isMemInst i2 h_i2_store
          have h_i1_mo_i2 := pposa_to_mo of ew h_instOrder i1 i2
            (pposa_ld_st ew.aa ew.po i1 i2 a h_i1_load h_i2_store h_po h_addr1 h_addr2) h_i1_mem' h_i2_mem'
          exact ew.mo.irrefl i2 (ew.mo.trans i2 i1 i2 h_mo_i2_i1 h_i1_mo_i2)
      · have h_w_mem := isStore_implies_isMemInst w h_w_store
        have h_i2_mem := isStore_implies_isMemInst i2 h_i2_store
        cases ew.mo.total w i2 h_w_mem h_i2_mem h_eq with
        | inl h_mo =>
          exact eco_fr ew i1 i2 w h_i1_load h_i2_store h_rf h_mo
            (by simp [Instruction.sameAddrWith, h_w_addr, h_addr2])
        | inr h_i2_mo_w =>
          exfalso
          have h_i1_mem' := isLoad_implies_isMemInst i1 h_i1_load
          have h_i2_mem' := isStore_implies_isMemInst i2 h_i2_store
          have h_i1_mo_i2 := pposa_to_mo of ew h_instOrder i1 i2
            (pposa_ld_st ew.aa ew.po i1 i2 a h_i1_load h_i2_store h_po h_addr1 h_addr2) h_i1_mem' h_i2_mem'
          have h_vis := h_loadValue w i1 a h_w_addr h_addr1 h_w_store h_i1_load h_rf
          cases h_vis.1 with
          | inl h_po_w_i1 =>
            have h_w_mo_i2 := pposa_to_mo of ew h_instOrder w i2
              (pposa_st_st ew.aa ew.po w i2 a h_w_store h_i2_store
                (ew.po.trans w i1 i2 h_po_w_i1 h_po) h_w_addr h_addr2) h_w_mem h_i2_mem'
            exact ew.mo.irrefl w (ew.mo.trans w i2 w h_w_mo_i2 h_i2_mo_w)
          | inr h_mo_w_i1 =>
            exact ew.mo.irrefl w (ew.mo.trans w i1 w h_mo_w_i1 (ew.mo.trans i1 i2 w h_i1_mo_i2 h_i2_mo_w))
  | inr h_i1_store => cases h_i2_mem with
    | inl h_i2_load =>
      obtain ⟨w, h_rf⟩ := ew.rf.coverage i2 h_i2_load (by simp [h_addr2] : (ew.aa i2.id).isSome)
      have h_w_store := (ew.rf.storeToLoad w i2 h_rf).1
      have h_w_addr := rf_same_addr ew w i2 a h_rf h_addr2
      by_cases h_eq : i1 = w
      · subst h_eq
        left; right; unfold composeRel reflTransClosure
        exact ⟨i1, Or.inl rfl, h_rf⟩
      · have h_i1_mem' := isStore_implies_isMemInst i1 h_i1_store
        have h_w_mem := isStore_implies_isMemInst w h_w_store
        cases ew.mo.total i1 w h_i1_mem' h_w_mem h_eq with
        | inl h_mo =>
          exact eco_co_star_rf ew i1 w i2 h_i1_store h_w_store h_mo h_rf
            (by simp [Instruction.sameAddrWith, h_addr1, h_w_addr])
        | inr h_w_mo_i1 =>
          exfalso
          have h_vis := h_loadValue w i2 a h_w_addr h_addr2 h_w_store h_i2_load h_rf
          cases h_vis.2 i1 h_i1_store h_addr1 (Or.inl h_po) with
          | inl h_i1_mo_w' => exact ew.mo.irrefl w (ew.mo.trans w i1 w h_w_mo_i1 h_i1_mo_w')
          | inr h_i1_eq_w' => exact h_eq h_i1_eq_w'
    | inr h_i2_store =>
      have h_i1_mem := isStore_implies_isMemInst i1 h_i1_store
      have h_i2_mem := isStore_implies_isMemInst i2 h_i2_store
      have h_neq : i1 ≠ i2 := by intro h_eq; subst h_eq; exact ew.po.irrefl i1 h_po
      cases ew.mo.total i1 i2 h_i1_mem h_i2_mem h_neq with
      | inl h_mo =>
        left; left; left
        exact ⟨h_i1_store, h_i2_store, by simp [Instruction.sameAddrWith, h_addr1, h_addr2], h_mo⟩
      | inr h_mo_rev =>
        exfalso
        have h_i1_mo_i2 := pposa_to_mo of ew h_instOrder i1 i2
          (pposa_st_st ew.aa ew.po i1 i2 a h_i1_store h_i2_store h_po h_addr1 h_addr2) h_i1_mem h_i2_mem
        exact ew.mo.irrefl i2 (ew.mo.trans i2 i1 i2 h_mo_rev h_i1_mo_i2)

end GamI2e
