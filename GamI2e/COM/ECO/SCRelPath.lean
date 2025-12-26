/-
COM: SC-Rel Path Utilities

This module provides utilities for reasoning about paths in the SC-per-Location
relation, including:
- SCRelLen: Length-indexed TransGen paths
- Path decomposition lemmas
- Load chain and store path analysis
- The key lemma sc_rel_store_to_load_rf_store_ordered
-/

import GamI2e.COM.ECO.SCRel

namespace GamI2e

/-- Helper: first edge of TransGen -/
theorem transGen_first_edge' {α : Type} {r : α → α → Prop} (a b : α)
    (h : Relation.TransGen r a b) :
    ∃ c, r a c ∧ (c = b ∨ Relation.TransGen r c b) := by
  induction h with
  | single h_edge => exact ⟨_, h_edge, Or.inl rfl⟩
  | tail h_trans h_last ih =>
    obtain ⟨c, h_first, h_rest⟩ := ih
    cases h_rest with
    | inl h_eq => subst h_eq; exact ⟨c, h_first, Or.inr (Relation.TransGen.single h_last)⟩
    | inr h_trans_cy => exact ⟨c, h_first, Or.inr (Relation.TransGen.tail h_trans_cy h_last)⟩

/-- Length-indexed TransGen for sc_rel -/
inductive SCRelLen (ew : ExecutionWitness) : Instruction → Instruction → Nat → Prop
  | single {a b : Instruction} : sc_rel ew a b → SCRelLen ew a b 1
  | tail {a b c : Instruction} {n : Nat} : SCRelLen ew a b n → sc_rel ew b c → SCRelLen ew a c (n + 1)

/-- Every TransGen sc_rel path has some length -/
theorem sc_rel_transgen_has_length (ew : ExecutionWitness) (a b : Instruction)
    (h : Relation.TransGen (sc_rel ew) a b) : ∃ n, SCRelLen ew a b n := by
  induction h with
  | single h_edge => exact ⟨1, SCRelLen.single h_edge⟩
  | tail _ h_last ih =>
    obtain ⟨n, h_len⟩ := ih
    exact ⟨n + 1, SCRelLen.tail h_len h_last⟩

/-- SCRelLen implies TransGen -/
theorem sc_rel_len_to_transgen (ew : ExecutionWitness) (a b : Instruction) (n : Nat)
    (h : SCRelLen ew a b n) : Relation.TransGen (sc_rel ew) a b := by
  induction h with
  | single h_edge => exact Relation.TransGen.single h_edge
  | tail _ h_last ih => exact Relation.TransGen.tail ih h_last

/-- Get first edge of SCRelLen path -/
theorem sc_rel_len_first_edge (ew : ExecutionWitness) (a : Instruction) {b : Instruction} {n : Nat}
    (h : SCRelLen ew a b n) : ∃ c, sc_rel ew a c ∧ (c = b ∨ ∃ m, m < n ∧ SCRelLen ew c b m) := by
  induction h with
  | single h_edge => exact ⟨_, h_edge, Or.inl rfl⟩
  | tail h_rest h_last ih =>
    rename_i mid endpoint n_rest
    obtain ⟨c, h_first, h_rest_or_eq⟩ := ih
    cases h_rest_or_eq with
    | inl h_eq =>
      subst h_eq
      have h_lt : 1 < n_rest + 1 := by
        have h_pos : 0 < n_rest := by
          cases h_rest with
          | single _ => exact Nat.zero_lt_one
          | tail _ _ => exact Nat.zero_lt_succ _
        exact Nat.add_lt_add_right h_pos 1
      exact ⟨c, h_first, Or.inr ⟨1, h_lt, SCRelLen.single h_last⟩⟩
    | inr h_exists =>
      obtain ⟨m, h_m_lt, h_path_m⟩ := h_exists
      exact ⟨c, h_first, Or.inr ⟨m + 1, Nat.add_lt_add_right h_m_lt 1, SCRelLen.tail h_path_m h_last⟩⟩

/-- Get last edge of SCRelLen path -/
theorem sc_rel_len_last_edge (ew : ExecutionWitness) (a b : Instruction) (n : Nat)
    (h : SCRelLen ew a b n) : ∃ c, sc_rel ew c b ∧ (a = c ∨ ∃ m, m < n ∧ SCRelLen ew a c m) := by
  induction h with
  | single h_edge => exact ⟨a, h_edge, Or.inl rfl⟩
  | tail h_rest h_last ih =>
    rename_i mid b' n_rest
    -- The last edge is h_last : mid → b'
    -- We need to show ∃ c, sc_rel c b' ∧ (a = c ∨ ...)
    -- c = mid works: sc_rel mid b', and we have h_rest : SCRelLen a mid n_rest
    exact ⟨mid, h_last, Or.inr ⟨n_rest, Nat.lt_succ_self n_rest, h_rest⟩⟩

/-- Lift TransGen through a monotone function -/
theorem transgen_lift {α : Type} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) (a b : α)
    (h_trans : Relation.TransGen r a b) : Relation.TransGen s a b := by
  induction h_trans with
  | single h_edge => exact Relation.TransGen.single (h _ _ h_edge)
  | tail _ h_last ih => exact Relation.TransGen.tail ih (h _ _ h_last)

/-- For load-load poloc, the stores that rf into them are mo-ordered (or equal).
    This is the key property from eco_poloc that we need for the consecutive loads case. -/
private theorem poloc_load_load_rf_stores_ordered (of : OrderedFunc) (ew : ExecutionWitness)
    (h_loadValue : satisfies_LoadValue ew)
    (h_instOrder : satisfies_InstOrder of ew)
    (l1 l2 : Instruction) (h_l1 : l1.isLoad = true) (h_l2 : l2.isLoad = true)
    (h_poloc : programOrderLoc ew.aa ew.po l1 l2)
    (w1 w2 : Instruction) (h_rf1 : ew.rf.rel w1 l1) (h_rf2 : ew.rf.rel w2 l2) :
    w1 = w2 ∨ ew.mo.rel w1 w2 := by
  have h_w1_store := (ew.rf.storeToLoad w1 l1 h_rf1).1
  have h_w2_store := (ew.rf.storeToLoad w2 l2 h_rf2).1
  by_cases h_eq : w1 = w2
  · exact Or.inl h_eq
  · right
    have h_w1_mem := isStore_implies_isMemInst w1 h_w1_store
    have h_w2_mem := isStore_implies_isMemInst w2 h_w2_store
    -- Get address info from poloc
    unfold programOrderLoc at h_poloc
    obtain ⟨h_po, h_same, h_l1_mem, h_l2_mem⟩ := h_poloc
    simp [Instruction.sameAddrWith] at h_same
    cases h_l1_addr : ew.aa l1.id with
    | none => simp [h_l1_addr] at h_same
    | some a =>
      cases h_l2_addr : ew.aa l2.id with
      | none => simp [h_l1_addr, h_l2_addr] at h_same
      | some a2 =>
        simp [h_l1_addr, h_l2_addr] at h_same
        have h_a_eq : a = a2 := h_same
        subst h_a_eq
        have h_w1_addr := rf_same_addr ew w1 l1 a h_rf1 h_l1_addr
        have h_w2_addr := rf_same_addr ew w2 l2 a h_rf2 h_l2_addr
        -- By mo total, either w1 mo w2 or w2 mo w1
        cases ew.mo.total w1 w2 h_w1_mem h_w2_mem h_eq with
        | inl h_mo => exact h_mo
        | inr h_w2_mo_w1 =>
          -- Contradiction: w2 mo w1 violates LoadValue
          exfalso
          have h_vis_w1 := h_loadValue w1 l1 a h_w1_addr h_l1_addr h_w1_store h_l1 h_rf1
          cases h_vis_w1.1 with
          | inl h_po_w1_l1 =>
            have h_vis_w2 := h_loadValue w2 l2 a h_w2_addr h_l2_addr h_w2_store h_l2 h_rf2
            -- w1 is po-before l1, and l1 po l2, so w1 po l2
            -- If w1 mo w2, then w1 is not maximal for l2, contradicting that w2 rf l2
            cases h_vis_w2.2 w1 h_w1_store h_w1_addr (Or.inl (ew.po.trans w1 l1 l2 h_po_w1_l1 h_po)) with
            | inl h_mo => exact ew.mo.irrefl w2 (ew.mo.trans w2 w1 w2 h_w2_mo_w1 h_mo)
            | inr h_eq' => exact h_eq h_eq'
          | inr h_mo_w1_l1 =>
            -- w1 mo l1, check for intervening store
            by_cases h_int : ∃ s, s.isStore = true ∧ s.sameAddrWith ew.aa l1 ∧
                                   ew.po.rel l1 s ∧ ew.po.rel s l2
            · obtain ⟨s, h_s_st, h_s_same, h_po_l1_s, h_po_s_l2⟩ := h_int
              have h_s_addr : ew.aa s.id = some a := by
                simp [Instruction.sameAddrWith] at h_s_same
                cases h_s_id : ew.aa s.id with
                | none => simp [h_s_id, h_l1_addr] at h_s_same
                | some as => simp [h_s_id, h_l1_addr] at h_s_same; cases h_s_same; rfl
              have h_vis_w2 := h_loadValue w2 l2 a h_w2_addr h_l2_addr h_w2_store h_l2 h_rf2
              have h_s_mem := isStore_implies_isMemInst s h_s_st
              have h_l1_mem' := isLoad_implies_isMemInst l1 h_l1
              have h_pposa : preservedSameAddrOrder ew.aa ew.po l1 s := by
                left; exact ⟨h_l1, h_s_st, h_po_l1_s, by simp [Instruction.sameAddrWith, h_l1_addr, h_s_addr]⟩
              have h_l1_mo_s := h_instOrder l1 s (pposa_subset_ppo ew.aa of ew.po l1 s h_pposa) h_l1_mem' h_s_mem
              have h_neq : l1 ≠ s := by
                intro h_eq; rw [h_eq] at h_l1
                simp only [Instruction.isLoad, Instruction.isStore] at h_l1 h_s_st
                cases h : s.instType <;> simp [h] at h_l1 h_s_st
              cases ew.mo.total s l1 h_s_mem h_l1_mem' (Ne.symm h_neq) with
              | inl h_mo => exact ew.mo.irrefl s (ew.mo.trans s l1 s h_mo h_l1_mo_s)
              | inr _ =>
                cases h_vis_w2.2 s h_s_st h_s_addr (Or.inl h_po_s_l2) with
                | inl h_mo =>
                  exact ew.mo.irrefl l1 (ew.mo.trans l1 w1 l1
                    (ew.mo.trans l1 w2 w1 (ew.mo.trans l1 s w2 h_l1_mo_s h_mo) h_w2_mo_w1) h_mo_w1_l1)
                | inr h_eq' =>
                  exact ew.mo.irrefl l1 (ew.mo.trans l1 w1 l1
                    (ew.mo.trans l1 s w1 h_l1_mo_s (h_eq' ▸ h_w2_mo_w1)) h_mo_w1_l1)
            · -- No intervening store: l1 pposa l2
              have h_l1_mem' := isLoad_implies_isMemInst l1 h_l1
              have h_l2_mem' := isLoad_implies_isMemInst l2 h_l2
              have h_pposa : preservedSameAddrOrder ew.aa ew.po l1 l2 := by
                right; right; exact ⟨h_l1, h_l2, h_po, by simp [Instruction.sameAddrWith, h_l1_addr, h_l2_addr], h_int⟩
              have h_l1_mo_l2 := h_instOrder l1 l2 (pposa_subset_ppo ew.aa of ew.po l1 l2 h_pposa) h_l1_mem' h_l2_mem'
              have h_vis_w2 := h_loadValue w2 l2 a h_w2_addr h_l2_addr h_w2_store h_l2 h_rf2
              cases h_vis_w2.2 w1 h_w1_store h_w1_addr (Or.inr (ew.mo.trans w1 l1 l2 h_mo_w1_l1 h_l1_mo_l2)) with
              | inl h_mo => exact ew.mo.irrefl w2 (ew.mo.trans w2 w1 w2 h_w2_mo_w1 h_mo)
              | inr h_eq' => exact h_eq h_eq'

/-- For a chain of loads connected by sc_rel (assuming all nodes are loads),
    the rf-stores are mo-ordered.
    Given l1 →+ l2 where both are loads, if w1 rf l1 and w2 rf l2, then w1 = w2 or mo w1 w2.

    Key insight: between loads, sc_rel can only be poloc (rf/co source is store,
    fr target is store). So we can apply poloc_load_load_rf_stores_ordered inductively.

    Note: This lemma assumes all intermediate nodes are loads. For general paths,
    use this in contexts where this is guaranteed (e.g., after sc_rel_last_store_in_path_to_load). -/
private theorem sc_rel_loads_chain_rf_stores_ordered (of : OrderedFunc) (ew : ExecutionWitness)
    (h_loadValue : satisfies_LoadValue ew)
    (h_instOrder : satisfies_InstOrder of ew)
    (l1 : Instruction) (h_l1 : l1.isLoad = true)
    {l2 : Instruction} (h_l2 : l2.isLoad = true)
    (h_path : Relation.TransGen (sc_rel ew) l1 l2)
    -- Hypothesis: all nodes in the path are loads (needed for induction to work)
    (h_all_loads : ∀ x, Relation.TransGen (sc_rel ew) l1 x → Relation.TransGen (sc_rel ew) x l2 → x.isLoad = true)
    (w1 w2 : Instruction) (h_rf1 : ew.rf.rel w1 l1) (h_rf2 : ew.rf.rel w2 l2) :
    w1 = w2 ∨ ew.mo.rel w1 w2 := by
  induction h_path generalizing w2 with
  | single h_edge =>
    -- Single edge l1 → l2, must be poloc
    have h_poloc := sc_rel_load_load_is_poloc ew l1 _ h_l1 h_l2 h_edge
    exact poloc_load_load_rf_stores_ordered of ew h_loadValue h_instOrder l1 _ h_l1 h_l2 h_poloc w1 w2 h_rf1 h_rf2
  | tail h_rest h_last ih =>
    rename_i mid endpoint
    -- Path l1 →+ mid → endpoint
    -- mid must be a load by h_all_loads
    have h_mid_load : mid.isLoad = true := by
      apply h_all_loads mid
      · exact h_rest
      · exact Relation.TransGen.single h_last
    have h_poloc := sc_rel_load_load_is_poloc ew mid endpoint h_mid_load h_l2 h_last
    -- Get rf-store into mid
    have h_mid_has_addr : (ew.aa mid.id).isSome := by
      have h_same := h_poloc.2.1
      simp [Instruction.sameAddrWith] at h_same
      cases h_mid_addr : ew.aa mid.id with
      | none => simp [h_mid_addr] at h_same
      | some _ => rfl
    obtain ⟨w_mid, h_rf_mid⟩ := ew.rf.coverage mid h_mid_load h_mid_has_addr
    -- By IH: w1 = w_mid or mo w1 w_mid
    have h_all_loads' : ∀ x, Relation.TransGen (sc_rel ew) l1 x → Relation.TransGen (sc_rel ew) x mid → x.isLoad = true := by
      intro x h_from h_to
      apply h_all_loads x h_from
      exact Relation.TransGen.tail h_to h_last
    have h_w1_wmid := ih h_mid_load h_all_loads' w_mid h_rf_mid
    -- By poloc_load_load_rf_stores_ordered: w_mid = w2 or mo w_mid w2
    have h_wmid_w2 := poloc_load_load_rf_stores_ordered of ew h_loadValue h_instOrder
      mid endpoint h_mid_load h_l2 h_poloc w_mid w2 h_rf_mid h_rf2
    -- Compose
    cases h_w1_wmid with
    | inl h_eq1 =>
      cases h_wmid_w2 with
      | inl h_eq2 => exact Or.inl (h_eq1.trans h_eq2)
      | inr h_mo2 => exact Or.inr (h_eq1 ▸ h_mo2)
    | inr h_mo1 =>
      cases h_wmid_w2 with
      | inl h_eq2 => exact Or.inr (h_eq2 ▸ h_mo1)
      | inr h_mo2 => exact Or.inr (ew.mo.trans w1 w_mid w2 h_mo1 h_mo2)

/-- Helper: TransGen is irreflexive for strict relations -/
private theorem transGen_irrefl_of_acyclic {α : Type} {r : α → α → Prop}
    (h_acyclic : ∀ x, ¬Relation.TransGen r x x) (x : α) : ¬Relation.TransGen r x x :=
  h_acyclic x

/-- Helper: transgen of po implies po -/
theorem po_transgen_to_po (po : ProgramOrder) (a b : Instruction)
    (h : Relation.TransGen po.rel a b) : po.rel a b := by
  induction h with
  | single h => exact h
  | tail _ h_last ih => exact po.trans _ _ _ ih h_last

/-- Poloc path implies po path, which is acyclic -/
private theorem poloc_transGen_irrefl (ew : ExecutionWitness) (x : Instruction) :
    ¬Relation.TransGen (programOrderLoc ew.aa ew.po) x x := by
  intro h_cycle
  have h_po_cycle : Relation.TransGen ew.po.rel x x := transgen_lift (fun a b h => h.1) x x h_cycle
  have h_po : ew.po.rel x x := po_transgen_to_po ew.po x x h_po_cycle
  exact ew.po.irrefl x h_po

/-- Find last store in sc_rel path ending at a load.
    Given path s1 →n l where s1 is a store and l is a load,
    find the last store w in the path such that s1 →* w and w →+ l.

    Returns SCRelLen paths (not TransGen) to enable IH application. -/
private theorem sc_rel_last_store_in_path_to_load (of : OrderedFunc) (ew : ExecutionWitness)
    (_h_instOrder : satisfies_InstOrder of ew)
    (_h_loadValue : satisfies_LoadValue ew)
    (s1 : Instruction)
    (h_s1 : s1.isStore = true)
    {endpoint : Instruction} (h_endpoint_load : endpoint.isLoad = true)
    {n : Nat} (h_path : SCRelLen ew s1 endpoint n) :
    ∃ w m, w.isStore = true ∧
         (s1 = w ∨ ∃ k, k < n ∧ SCRelLen ew s1 w k) ∧
         m > 0 ∧ m ≤ n ∧ SCRelLen ew w endpoint m := by
  induction h_path with
  | single h_edge =>
    -- Single edge s1 → endpoint (n = 1)
    -- Edge to a load must be rf or poloc
    -- s1 is the last store, path length from w to endpoint is 1
    exact ⟨s1, 1, h_s1, Or.inl rfl, Nat.one_pos, Nat.le_refl 1, SCRelLen.single h_edge⟩
  | tail h_rest h_last ih =>
    rename_i mid endpoint n_rest
    -- Path s1 →n_rest mid → endpoint where n = n_rest + 1
    by_cases h_mid_store : mid.isStore = true
    · -- mid is a store: mid is the last store before endpoint
      -- Path from mid to endpoint has length 1
      exact ⟨mid, 1, h_mid_store, Or.inr ⟨n_rest, Nat.lt_succ_self n_rest, h_rest⟩,
             Nat.one_pos, Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n_rest),
             SCRelLen.single h_last⟩
    · -- mid is not a store
      by_cases h_mid_load : mid.isLoad = true
      · -- mid is a load: recurse on s1 →n_rest mid
        obtain ⟨w, m, h_w_store, h_path_s1_w, h_m_pos, h_m_le, h_path_w_mid⟩ := ih h_mid_load
        -- Extend path w →m mid → endpoint to get w →(m+1) endpoint
        have h_path_w_endpoint : SCRelLen ew w endpoint (m + 1) := SCRelLen.tail h_path_w_mid h_last
        cases h_path_s1_w with
        | inl h_eq =>
          exact ⟨w, m + 1, h_w_store, Or.inl h_eq,
                 Nat.succ_pos m, Nat.succ_le_succ h_m_le, h_path_w_endpoint⟩
        | inr h_exists =>
          obtain ⟨k, h_k_lt, h_path_k⟩ := h_exists
          exact ⟨w, m + 1, h_w_store,
                 Or.inr ⟨k, Nat.lt_trans h_k_lt (Nat.lt_succ_self n_rest), h_path_k⟩,
                 Nat.succ_pos m, Nat.succ_le_succ h_m_le, h_path_w_endpoint⟩
      · -- mid is neither load nor store: contradiction
        obtain ⟨prev, h_prev_edge, _⟩ := sc_rel_len_last_edge ew s1 mid n_rest h_rest
        unfold sc_rel unionRel at h_prev_edge
        cases h_prev_edge with
        | inl h123 =>
          cases h123 with
          | inl h12 =>
            cases h12 with
            | inl h_rf => exact absurd (rf_target_is_load ew.aa ew.rf prev mid h_rf) h_mid_load
            | inr h_co => exact absurd (co_target_is_store ew.aa ew.mo prev mid h_co) h_mid_store
          | inr h_fr => exact absurd (fr_target_is_store ew.aa ew.rf ew.mo prev mid h_fr) h_mid_store
        | inr h_poloc =>
          have h_mid_mem := h_poloc.2.2.2
          rw [isMemInst_iff_load_or_store] at h_mid_mem
          cases h_mid_mem with
          | inl h => exact absurd h h_mid_load
          | inr h => exact absurd h h_mid_store

/-- Helper: get last edge of a TransGen path -/
private theorem transGen_last_edge' {α : Type} {r : α → α → Prop} (a : α) {b : α}
    (h_path : Relation.TransGen r a b) :
    ∃ c, r c b ∧ (a = c ∨ Relation.TransGen r a c) := by
  cases h_path with
  | single h_edge => exact ⟨a, h_edge, Or.inl rfl⟩
  | tail h_rest h_last =>
    rename_i mid
    exact ⟨mid, h_last, Or.inr h_rest⟩

/-- Key lemma: for a path l1 →+ l2 between loads where the path was constructed
    by going through only loads (i.e., no fr edges which would introduce stores),
    all intermediate nodes are loads.

    This is proven by simple induction: each edge from a load either goes to
    another load (poloc) or to a store (fr). If we reach a store via fr, we
    cannot return to a load without going through rf, making that store the
    "source" of the load. But since we're on a path from l1 to l2 both loads,
    if there's a store in between, the path would look like:
    l1 →fr s → ... →rf l → ... → l2
    meaning there's an rf edge from store to load.

    For the SC-per-Location proof, we use this indirectly: we know the path
    from "first" (a load after the last store w) to "mid" (a load) goes through
    only loads because any store would contradict w being the "last store". -/
private theorem sc_rel_between_loads_is_poloc_path (ew : ExecutionWitness)
    (l1 : Instruction) (_h_l1 : l1.isLoad = true)
    {l2 : Instruction} (_h_l2 : l2.isLoad = true)
    (_h_path : Relation.TransGen (sc_rel ew) l1 l2)
    -- Key hypothesis: the path doesn't go through stores
    (h_no_stores : ∀ x, Relation.TransGen (sc_rel ew) l1 x →
                        Relation.TransGen (sc_rel ew) x l2 →
                        ¬x.isStore = true) :
    ∀ x, Relation.TransGen (sc_rel ew) l1 x →
         Relation.TransGen (sc_rel ew) x l2 →
         x.isLoad = true := by
  intro x h_from_l1 h_to_l2
  -- x is a mem inst (from being on sc_rel path)
  -- and x is not a store (by h_no_stores)
  -- therefore x is a load
  -- Get the last edge into x
  obtain ⟨prev, h_last_edge, _⟩ := transGen_last_edge' l1 h_from_l1
  have h_x_mem : x.isMemInst = true := by
    unfold sc_rel unionRel at h_last_edge
    cases h_last_edge with
    | inl h123 =>
      cases h123 with
      | inl h12 =>
        cases h12 with
        | inl h_rf => exact isLoad_implies_isMemInst x (rf_target_is_load ew.aa ew.rf prev x h_rf)
        | inr h_co => exact isStore_implies_isMemInst x (co_target_is_store ew.aa ew.mo prev x h_co)
      | inr h_fr => exact isStore_implies_isMemInst x (fr_target_is_store ew.aa ew.rf ew.mo prev x h_fr)
    | inr h_poloc => exact h_poloc.2.2.2
  rw [isMemInst_iff_load_or_store] at h_x_mem
  cases h_x_mem with
  | inl h => exact h
  | inr h_x_store => exact absurd h_x_store (h_no_stores x h_from_l1 h_to_l2)

/-- Helper: compose mo relations with equality cases -/
def compose_mo_with_eq (ew : ExecutionWitness) (a b c : Instruction)
    (h_ab : a = b ∨ ew.mo.rel a b) (h_bc : b = c ∨ ew.mo.rel b c) : a = c ∨ ew.mo.rel a c :=
  match h_ab, h_bc with
  | Or.inl h_eq1, Or.inl h_eq2 => Or.inl (h_eq1.trans h_eq2)
  | Or.inl h_eq1, Or.inr h_mo2 => Or.inr (h_eq1 ▸ h_mo2)
  | Or.inr h_mo1, Or.inl h_eq2 => Or.inr (h_eq2 ▸ h_mo1)
  | Or.inr h_mo1, Or.inr h_mo2 => Or.inr (ew.mo.trans a b c h_mo1 h_mo2)

/-- Key lemma: For an SCRelLen path from store w to load l, if w' is the rf-store into l,
    then w = w' or mo w w'.

    This is the paper's insight: we don't track the specific path, just the rf-stores.
    By strong induction on path length using LAST edge decomposition. -/
theorem sc_rel_store_to_load_rf_store_ordered (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew)
    (h_loadValue : satisfies_LoadValue ew)
    (m : Nat) :
    ∀ (w : Instruction) (_h_w_store : w.isStore = true)
      (l : Instruction) (_h_l_load : l.isLoad = true)
      (_h_path : SCRelLen ew w l m)
      (w' : Instruction) (_h_rf : ew.rf.rel w' l),
    w = w' ∨ ew.mo.rel w w' := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro w h_w_store l h_l_load h_path w' h_rf
    -- Get last edge of path
    obtain ⟨prev, h_last_edge, h_prefix⟩ := sc_rel_len_last_edge ew w l m h_path
    cases h_prefix with
    | inl h_eq_w_prev =>
      -- Single edge: w → l directly (prev = w)
      subst h_eq_w_prev
      cases sc_rel_store_to_load_rf_or_poloc ew w l h_w_store h_l_load h_last_edge with
      | inl h_rf_w_l =>
        exact Or.inl (ew.rf.functional l w w' h_rf_w_l h_rf)
      | inr h_poloc_w_l =>
        obtain ⟨z, h_z_rel, h_rf_z_l⟩ := poloc_store_load_gives_rf of ew h_loadValue h_instOrder
          w l h_w_store h_l_load h_poloc_w_l
        have h_eq_z : z = w' := ew.rf.functional l z w' h_rf_z_l h_rf
        cases h_z_rel with
        | inl h_eq_w_z => exact Or.inl (h_eq_w_z.symm.trans h_eq_z)
        | inr h_co_trans =>
          have h_mo : ew.mo.rel w w' := by
            have h_lift := transgen_lift (fun a b h_co => h_co.2.2.2) w z h_co_trans
            exact h_eq_z ▸ mo_transgen_to_mo ew.mo w z h_lift
          exact Or.inr h_mo
    | inr h_multi =>
      -- Multi-edge: w →+ prev → l
      obtain ⟨m', h_m'_lt, h_path_to_prev⟩ := h_multi
      by_cases h_prev_load : prev.isLoad = true
      · -- prev is a load
        have h_prev_has_addr : (ew.aa prev.id).isSome := by
          cases sc_rel_edge_to_load ew prev l h_l_load h_last_edge with
          | inl h_rf_prev_l =>
            have h := ew.rf.sameAddr prev l h_rf_prev_l
            simp [Instruction.sameAddrWith] at h
            cases h_p : ew.aa prev.id with
            | none =>
              cases h_ll : ew.aa l.id with
              | none => simp [h_ll, h_p] at h
              | some _ => simp [h_ll, h_p] at h
            | some _ => rfl
          | inr h_poloc =>
            have h_same := h_poloc.2.1
            simp [Instruction.sameAddrWith] at h_same
            cases h_p : ew.aa prev.id with
            | none =>
              cases h_ll : ew.aa l.id with
              | none => simp [h_ll, h_p] at h_same
              | some _ => simp [h_ll, h_p] at h_same
            | some _ => rfl
        obtain ⟨w_prev, h_rf_w_prev⟩ := ew.rf.coverage prev h_prev_load h_prev_has_addr
        have h_w_prev_store := rf_source_is_store ew.aa ew.rf w_prev prev h_rf_w_prev
        -- By IH: w = w_prev or mo w w_prev
        have h_w_w_prev : w = w_prev ∨ ew.mo.rel w w_prev :=
          ih m' h_m'_lt w h_w_store prev h_prev_load h_path_to_prev w_prev h_rf_w_prev
        -- By poloc_load_load_rf_stores_ordered: w_prev = w' or mo w_prev w'
        have h_poloc_prev_l := sc_rel_load_load_is_poloc ew prev l h_prev_load h_l_load h_last_edge
        have h_w_prev_w' := poloc_load_load_rf_stores_ordered of ew h_loadValue h_instOrder
          prev l h_prev_load h_l_load h_poloc_prev_l w_prev w' h_rf_w_prev h_rf
        exact compose_mo_with_eq ew w w_prev w' h_w_w_prev h_w_prev_w'
      · -- prev is not a load
        by_cases h_prev_store : prev.isStore = true
        · -- prev is a store: edge prev → l where prev is store, l is load
          cases sc_rel_store_to_load_rf_or_poloc ew prev l h_prev_store h_l_load h_last_edge with
          | inl h_rf_prev_l =>
            -- rf prev l, so prev = w' (by functionality)
            have h_eq_prev_w' := ew.rf.functional l prev w' h_rf_prev_l h_rf
            -- Need mo w prev. We have w →m' prev (stores) with m' < m.
            -- Prove by nested strong induction: store-to-store path gives mo
            have h_mo_w_prev : w = prev ∨ ew.mo.rel w prev := by
              clear h_l_load h_path h_rf h_last_edge h_rf_prev_l h_eq_prev_w'
              -- Strong induction on m'
              induction m' using Nat.strongRecOn generalizing w prev with
              | _ n ih_inner =>
                obtain ⟨mid, h_edge, h_prefix_inner⟩ := sc_rel_len_last_edge ew w prev n h_path_to_prev
                cases h_prefix_inner with
                | inl h_eq_w_mid =>
                  -- Single edge w → prev
                  subst h_eq_w_mid
                  exact Or.inr (sc_rel_store_to_store_gives_mo of ew h_instOrder w prev h_w_store h_prev_store h_edge)
                | inr h_multi =>
                  obtain ⟨k, h_k_lt, h_path_k⟩ := h_multi
                  -- Need to determine if mid is store or load
                  by_cases h_mid_store_inner : mid.isStore = true
                  · -- mid is store: by IH, mo w mid; by single edge, mo mid prev; compose
                    have h_not_mid_load : ¬mid.isLoad = true := by
                      intro h; exact absurd h_mid_store_inner (load_not_store mid h)
                    have h_mo_w_mid : w = mid ∨ ew.mo.rel w mid :=
                      ih_inner k h_k_lt w h_w_store mid (Nat.lt_trans h_k_lt h_m'_lt) h_path_k h_not_mid_load h_mid_store_inner
                    have h_mo_mid_prev := sc_rel_store_to_store_gives_mo of ew h_instOrder mid prev h_mid_store_inner h_prev_store h_edge
                    exact compose_mo_with_eq ew w mid prev h_mo_w_mid (Or.inr h_mo_mid_prev)
                  · -- mid is not store: must be load (by sc_rel target analysis)
                    by_cases h_mid_load_inner : mid.isLoad = true
                    · -- mid is load: edge mid → prev (store) is fr or poloc
                      cases sc_rel_load_to_store_fr_or_poloc ew mid prev h_mid_load_inner h_prev_store h_edge with
                      | inl h_fr =>
                        obtain ⟨_, _, w_mid, h_rf_w_mid, _, h_mo_w_mid_prev⟩ := h_fr
                        have h_w_w_mid := ih k (Nat.lt_trans h_k_lt h_m'_lt) w h_w_store mid h_mid_load_inner h_path_k w_mid h_rf_w_mid
                        exact compose_mo_with_eq ew w w_mid prev h_w_w_mid (Or.inr h_mo_w_mid_prev)
                      | inr h_poloc =>
                        have h_fr := poloc_load_store_is_fr of ew h_loadValue h_instOrder mid prev h_mid_load_inner h_prev_store h_poloc
                        obtain ⟨_, _, w_mid, h_rf_w_mid, _, h_mo_w_mid_prev⟩ := h_fr
                        have h_w_w_mid := ih k (Nat.lt_trans h_k_lt h_m'_lt) w h_w_store mid h_mid_load_inner h_path_k w_mid h_rf_w_mid
                        exact compose_mo_with_eq ew w w_mid prev h_w_w_mid (Or.inr h_mo_w_mid_prev)
                    · exact absurd (sc_rel_edge_from_non_mem_absurd ew mid prev h_edge h_mid_load_inner h_mid_store_inner) id
            exact compose_mo_with_eq ew w prev w' h_mo_w_prev (Or.inl h_eq_prev_w')
          | inr h_poloc_prev_l =>
            obtain ⟨z, h_z_rel, h_rf_z_l⟩ := poloc_store_load_gives_rf of ew h_loadValue h_instOrder
              prev l h_prev_store h_l_load h_poloc_prev_l
            have h_eq_z := ew.rf.functional l z w' h_rf_z_l h_rf
            -- Need w = z or mo w z. But z is the rf-witness from poloc, related to prev.
            -- By z = prev or co+ prev z, and we need mo w prev first.
            have h_mo_w_prev : w = prev ∨ ew.mo.rel w prev := by
              clear h_l_load h_path h_rf h_last_edge h_poloc_prev_l h_z_rel h_rf_z_l h_eq_z
              induction m' using Nat.strongRecOn generalizing w prev with
              | _ n ih_inner =>
                obtain ⟨mid, h_edge, h_prefix_inner⟩ := sc_rel_len_last_edge ew w prev n h_path_to_prev
                cases h_prefix_inner with
                | inl h_eq_w_mid =>
                  subst h_eq_w_mid
                  exact Or.inr (sc_rel_store_to_store_gives_mo of ew h_instOrder w prev h_w_store h_prev_store h_edge)
                | inr h_multi =>
                  obtain ⟨k, h_k_lt, h_path_k⟩ := h_multi
                  by_cases h_mid_store_inner : mid.isStore = true
                  · have h_not_mid_load : ¬mid.isLoad = true := by
                      intro h; exact absurd h_mid_store_inner (load_not_store mid h)
                    have h_mo_w_mid := ih_inner k h_k_lt w h_w_store mid (Nat.lt_trans h_k_lt h_m'_lt) h_path_k h_not_mid_load h_mid_store_inner
                    have h_mo_mid_prev := sc_rel_store_to_store_gives_mo of ew h_instOrder mid prev h_mid_store_inner h_prev_store h_edge
                    exact compose_mo_with_eq ew w mid prev h_mo_w_mid (Or.inr h_mo_mid_prev)
                  · by_cases h_mid_load_inner : mid.isLoad = true
                    · cases sc_rel_load_to_store_fr_or_poloc ew mid prev h_mid_load_inner h_prev_store h_edge with
                      | inl h_fr =>
                        obtain ⟨_, _, w_mid, h_rf_w_mid, _, h_mo_w_mid_prev⟩ := h_fr
                        have h_w_w_mid := ih k (Nat.lt_trans h_k_lt h_m'_lt) w h_w_store mid h_mid_load_inner h_path_k w_mid h_rf_w_mid
                        exact compose_mo_with_eq ew w w_mid prev h_w_w_mid (Or.inr h_mo_w_mid_prev)
                      | inr h_poloc =>
                        have h_fr := poloc_load_store_is_fr of ew h_loadValue h_instOrder mid prev h_mid_load_inner h_prev_store h_poloc
                        obtain ⟨_, _, w_mid, h_rf_w_mid, _, h_mo_w_mid_prev⟩ := h_fr
                        have h_w_w_mid := ih k (Nat.lt_trans h_k_lt h_m'_lt) w h_w_store mid h_mid_load_inner h_path_k w_mid h_rf_w_mid
                        exact compose_mo_with_eq ew w w_mid prev h_w_w_mid (Or.inr h_mo_w_mid_prev)
                    · exact absurd (sc_rel_edge_from_non_mem_absurd ew mid prev h_edge h_mid_load_inner h_mid_store_inner) id
            cases h_z_rel with
            | inl h_eq_z_prev =>
              exact compose_mo_with_eq ew w prev w' h_mo_w_prev (Or.inl (h_eq_z_prev.symm.trans h_eq_z))
            | inr h_co_trans =>
              have h_mo_prev_z : ew.mo.rel prev z := by
                have h_lift := transgen_lift (fun a b h_co => h_co.2.2.2) prev z h_co_trans
                exact mo_transgen_to_mo ew.mo prev z h_lift
              exact h_eq_z ▸ compose_mo_with_eq ew w prev z h_mo_w_prev (Or.inr h_mo_prev_z)
        · exact absurd (sc_rel_edge_from_non_mem_absurd ew prev l h_last_edge h_prev_load h_prev_store) id

end GamI2e
