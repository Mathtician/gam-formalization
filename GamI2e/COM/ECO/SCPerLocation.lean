/-
COM: SC-per-Location Proof

This module contains the main SC-per-Location acyclicity proof:
- sc_rel_stores_transgen_to_mo: Store-to-store paths reduce to mo paths
- sc_rel_cycle_has_store: Any cycle contains at least one store
- sc_per_location_acyclic: Main theorem - acyclic(rf ∪ co ∪ fr ∪ poloc)
-/

import GamI2e.COM.ECO.SCRelPath

namespace GamI2e

/-- Length-indexed helper for sc_rel_stores_transgen_to_mo.
    Uses strong induction on path length.

    The key insight is: when we encounter a load in the path, we can
    "skip over" it using rf;fr ⊆ co ⊆ mo. -/
private theorem sc_rel_stores_transgen_to_mo_len (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew)
    (h_loadValue : satisfies_LoadValue ew)
    (n : Nat) :
    ∀ (s1 : Instruction) (_h_s1 : s1.isStore = true)
      {s2 : Instruction} (_h_s2 : s2.isStore = true)
      (_h_path : SCRelLen ew s1 s2 n),
    Relation.TransGen ew.mo.rel s1 s2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro s1 h_s1 s2 h_s2 h_path
    -- Get the last edge of the path
    obtain ⟨mid, h_last_edge, h_prefix⟩ := sc_rel_len_last_edge ew s1 s2 n h_path
    -- Case split on whether mid is a store or load
    by_cases h_mid_store : mid.isStore = true
    · -- mid is a store: straightforward
      have h_mo_mid_s2 := sc_rel_store_to_store_gives_mo of ew h_instOrder mid s2 h_mid_store h_s2 h_last_edge
      cases h_prefix with
      | inl h_eq =>
        exact h_eq ▸ Relation.TransGen.single h_mo_mid_s2
      | inr h_exists =>
        obtain ⟨k, h_k_lt, h_path_k⟩ := h_exists
        have h_mo_s1_mid := ih k h_k_lt s1 h_s1 h_mid_store h_path_k
        exact Relation.TransGen.tail h_mo_s1_mid h_mo_mid_s2
    · -- mid is not a store: must be a load (since sc_rel requires mem inst)
      by_cases h_mid_load : mid.isLoad = true
      · -- mid is a load
        -- The last edge mid → s2 is fr or poloc
        cases sc_rel_load_to_store_fr_or_poloc ew mid s2 h_mid_load h_s2 h_last_edge with
        | inl h_fr =>
          -- We have fr mid s2
          -- Find the rf edge into mid from the prefix path
          cases h_prefix with
          | inl h_eq =>
            -- s1 = mid, but s1 is a store and mid is a load - contradiction
            exact absurd h_s1 (load_not_store s1 (h_eq ▸ h_mid_load))
          | inr h_exists =>
            obtain ⟨k, h_k_lt, h_path_k⟩ := h_exists
            -- Path s1 →k mid where mid is a load
            -- Get the last edge of this prefix path
            obtain ⟨prev, h_prev_edge, h_prefix2⟩ := sc_rel_len_last_edge ew s1 mid k h_path_k
            -- Edge prev → mid where mid is a load: must be rf or poloc
            cases sc_rel_edge_to_load ew prev mid h_mid_load h_prev_edge with
            | inl h_rf_prev_mid =>
              -- We have rf prev mid and fr mid s2
              -- By rf;fr ⊆ co, get co prev s2
              have h_co_prev_s2 := rf_fr_gives_co ew.aa ew.rf ew.mo prev mid s2 h_rf_prev_mid h_fr
              have h_mo_prev_s2 := h_co_prev_s2.2.2.2
              have h_prev_store := rf_source_is_store ew.aa ew.rf prev mid h_rf_prev_mid
              cases h_prefix2 with
              | inl h_eq =>
                exact h_eq ▸ Relation.TransGen.single h_mo_prev_s2
              | inr h_exists2 =>
                obtain ⟨j, h_j_lt, h_path_j⟩ := h_exists2
                have h_mo_s1_prev := ih j (Nat.lt_trans h_j_lt h_k_lt) s1 h_s1 h_prev_store h_path_j
                exact Relation.TransGen.tail h_mo_s1_prev h_mo_prev_s2
            | inr h_poloc_prev_mid =>
              -- We have poloc prev mid where mid is a load
              -- By poloc_store_load_gives_rf (if prev is store) or eco analysis, get rf w mid
              by_cases h_prev_store : prev.isStore = true
              · -- prev is store, mid is load, poloc prev mid
                -- By poloc_store_load_gives_rf, get rf w mid with w = prev or co+ prev w
                obtain ⟨w, h_w_rel, h_rf_w_mid⟩ := poloc_store_load_gives_rf of ew h_loadValue h_instOrder
                  prev mid h_prev_store h_mid_load h_poloc_prev_mid
                have h_co_w_s2 := rf_fr_gives_co ew.aa ew.rf ew.mo w mid s2 h_rf_w_mid h_fr
                have h_mo_w_s2 := h_co_w_s2.2.2.2
                have h_w_store := rf_source_is_store ew.aa ew.rf w mid h_rf_w_mid
                cases h_w_rel with
                | inl h_eq =>
                  -- w = prev
                  cases h_prefix2 with
                  | inl h_eq2 =>
                    exact h_eq2 ▸ h_eq ▸ Relation.TransGen.single h_mo_w_s2
                  | inr h_exists2 =>
                    obtain ⟨j, h_j_lt, h_path_j⟩ := h_exists2
                    have h_mo_s1_w := ih j (Nat.lt_trans h_j_lt h_k_lt) s1 h_s1 (h_eq ▸ h_prev_store) h_path_j
                    exact Relation.TransGen.tail (h_eq ▸ h_mo_s1_w) h_mo_w_s2
                | inr h_co_trans =>
                  -- co+ prev w
                  have h_mo_prev_w : ew.mo.rel prev w := by
                    have h_lift : Relation.TransGen ew.mo.rel prev w :=
                      transgen_lift (fun a b h_co => h_co.2.2.2) prev w h_co_trans
                    exact mo_transgen_to_mo ew.mo prev w h_lift
                  cases h_prefix2 with
                  | inl h_eq2 =>
                    -- s1 = prev
                    exact h_eq2 ▸ Relation.TransGen.trans (Relation.TransGen.single h_mo_prev_w)
                      (Relation.TransGen.single h_mo_w_s2)
                  | inr h_exists2 =>
                    obtain ⟨j, h_j_lt, h_path_j⟩ := h_exists2
                    have h_mo_s1_prev := ih j (Nat.lt_trans h_j_lt h_k_lt) s1 h_s1 h_prev_store h_path_j
                    exact Relation.TransGen.tail (Relation.TransGen.tail h_mo_s1_prev h_mo_prev_w) h_mo_w_s2
              · -- prev is not a store
                by_cases h_prev_load : prev.isLoad = true
                · -- prev is a load, mid is a load, poloc prev mid
                  -- Get rf-store w' into mid
                  have h_mid_has_addr : (ew.aa mid.id).isSome := by
                    unfold programOrderLoc at h_poloc_prev_mid
                    have h_same := h_poloc_prev_mid.2.1
                    simp [Instruction.sameAddrWith] at h_same
                    cases h_mid_addr : ew.aa mid.id with
                    | none => simp [h_mid_addr] at h_same
                    | some _ => rfl
                  obtain ⟨w', h_rf_w'_mid⟩ := ew.rf.coverage mid h_mid_load h_mid_has_addr
                  have h_w'_store := rf_source_is_store ew.aa ew.rf w' mid h_rf_w'_mid
                  -- By rf w' mid and fr mid s2, get co w' s2
                  have h_co_w'_s2 := rf_fr_gives_co ew.aa ew.rf ew.mo w' mid s2 h_rf_w'_mid h_fr
                  have h_mo_w'_s2 := h_co_w'_s2.2.2.2
                  -- Use sc_rel_store_to_load_rf_store_ordered to get s1 = w' or mo s1 w'
                  have h_s1_w'_ordered := sc_rel_store_to_load_rf_store_ordered of ew h_instOrder h_loadValue
                    k s1 h_s1 mid h_mid_load h_path_k w' h_rf_w'_mid
                  -- Compose to get mo+ s1 s2
                  cases h_s1_w'_ordered with
                  | inl h_eq => exact h_eq ▸ Relation.TransGen.single h_mo_w'_s2
                  | inr h_mo => exact Relation.TransGen.tail (Relation.TransGen.single h_mo) h_mo_w'_s2
                · exact absurd (sc_rel_edge_from_non_mem_absurd ew prev mid h_prev_edge h_prev_load h_prev_store) id
        | inr h_poloc_mid_s2 =>
          -- poloc mid s2 where mid is load and s2 is store
          -- By poloc_load_store_is_fr, get fr mid s2
          have h_fr := poloc_load_store_is_fr of ew h_loadValue h_instOrder mid s2 h_mid_load h_s2 h_poloc_mid_s2
          -- Now same as the fr case above - recurse
          cases h_prefix with
          | inl h_eq =>
            exact absurd h_s1 (load_not_store s1 (h_eq ▸ h_mid_load))
          | inr h_exists =>
            obtain ⟨k, h_k_lt, h_path_k⟩ := h_exists
            obtain ⟨prev, h_prev_edge, h_prefix2⟩ := sc_rel_len_last_edge ew s1 mid k h_path_k
            cases sc_rel_edge_to_load ew prev mid h_mid_load h_prev_edge with
            | inl h_rf_prev_mid =>
              have h_co_prev_s2 := rf_fr_gives_co ew.aa ew.rf ew.mo prev mid s2 h_rf_prev_mid h_fr
              have h_mo_prev_s2 := h_co_prev_s2.2.2.2
              have h_prev_store := rf_source_is_store ew.aa ew.rf prev mid h_rf_prev_mid
              cases h_prefix2 with
              | inl h_eq =>
                exact h_eq ▸ Relation.TransGen.single h_mo_prev_s2
              | inr h_exists2 =>
                obtain ⟨j, h_j_lt, h_path_j⟩ := h_exists2
                have h_mo_s1_prev := ih j (Nat.lt_trans h_j_lt h_k_lt) s1 h_s1 h_prev_store h_path_j
                exact Relation.TransGen.tail h_mo_s1_prev h_mo_prev_s2
            | inr h_poloc_prev_mid =>
              by_cases h_prev_store : prev.isStore = true
              · obtain ⟨w, h_w_rel, h_rf_w_mid⟩ := poloc_store_load_gives_rf of ew h_loadValue h_instOrder
                  prev mid h_prev_store h_mid_load h_poloc_prev_mid
                have h_co_w_s2 := rf_fr_gives_co ew.aa ew.rf ew.mo w mid s2 h_rf_w_mid h_fr
                have h_mo_w_s2 := h_co_w_s2.2.2.2
                have h_w_store := rf_source_is_store ew.aa ew.rf w mid h_rf_w_mid
                cases h_w_rel with
                | inl h_eq =>
                  cases h_prefix2 with
                  | inl h_eq2 =>
                    exact h_eq2 ▸ h_eq ▸ Relation.TransGen.single h_mo_w_s2
                  | inr h_exists2 =>
                    obtain ⟨j, h_j_lt, h_path_j⟩ := h_exists2
                    have h_mo_s1_w := ih j (Nat.lt_trans h_j_lt h_k_lt) s1 h_s1 (h_eq ▸ h_prev_store) h_path_j
                    exact Relation.TransGen.tail (h_eq ▸ h_mo_s1_w) h_mo_w_s2
                | inr h_co_trans =>
                  have h_mo_prev_w : ew.mo.rel prev w := by
                    have h_lift : Relation.TransGen ew.mo.rel prev w :=
                      transgen_lift (fun a b h_co => h_co.2.2.2) prev w h_co_trans
                    exact mo_transgen_to_mo ew.mo prev w h_lift
                  cases h_prefix2 with
                  | inl h_eq2 =>
                    exact h_eq2 ▸ Relation.TransGen.trans (Relation.TransGen.single h_mo_prev_w)
                      (Relation.TransGen.single h_mo_w_s2)
                  | inr h_exists2 =>
                    obtain ⟨j, h_j_lt, h_path_j⟩ := h_exists2
                    have h_mo_s1_prev := ih j (Nat.lt_trans h_j_lt h_k_lt) s1 h_s1 h_prev_store h_path_j
                    exact Relation.TransGen.tail (Relation.TransGen.tail h_mo_s1_prev h_mo_prev_w) h_mo_w_s2
              · by_cases h_prev_load : prev.isLoad = true
                · -- prev is load, mid is load - consecutive loads case
                  -- Extract rf-store w' from fr mid s2
                  obtain ⟨_, _, w', h_rf_w'_mid, _, h_mo_w'_s2⟩ := h_fr
                  have h_w'_store := rf_source_is_store ew.aa ew.rf w' mid h_rf_w'_mid
                  -- Use sc_rel_store_to_load_rf_store_ordered to get s1 = w' or mo s1 w'
                  have h_s1_w'_ordered := sc_rel_store_to_load_rf_store_ordered of ew h_instOrder h_loadValue
                    k s1 h_s1 mid h_mid_load h_path_k w' h_rf_w'_mid
                  -- Compose to get mo+ s1 s2
                  cases h_s1_w'_ordered with
                  | inl h_eq => exact h_eq ▸ Relation.TransGen.single h_mo_w'_s2
                  | inr h_mo => exact Relation.TransGen.tail (Relation.TransGen.single h_mo) h_mo_w'_s2
                · exact absurd (sc_rel_edge_from_non_mem_absurd ew prev mid h_prev_edge h_prev_load h_prev_store) id
      · -- mid is neither load nor store - contradiction
        exact absurd (sc_rel_edge_from_non_mem_absurd ew mid s2 h_last_edge h_mid_load h_mid_store) id

/-- The SC-per-Location relation between stores gives mo path.

Key insight: any sc_rel path s1 →+ s2 between stores can be reduced to mo path.
Intermediate loads are "shortcut" using rf;fr ⊆ co ⊆ mo. -/
theorem sc_rel_stores_transgen_to_mo (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew)
    (h_loadValue : satisfies_LoadValue ew)
    (s1 s2 : Instruction) (h_s1 : s1.isStore = true) (h_s2 : s2.isStore = true)
    (h_path : Relation.TransGen (sc_rel ew) s1 s2) :
    Relation.TransGen ew.mo.rel s1 s2 := by
  obtain ⟨n, h_len⟩ := sc_rel_transgen_has_length ew s1 s2 h_path
  exact sc_rel_stores_transgen_to_mo_len of ew h_instOrder h_loadValue n s1 h_s1 h_s2 h_len

/-- Key lemma: In any sc_rel cycle, there exists a store.
    Proof: If all nodes were loads, all edges would be load-to-load poloc (since rf/co/fr
    all involve stores). But poloc ⊆ po, so we'd have a po cycle, contradicting po acyclicity. -/
theorem sc_rel_cycle_has_store (ew : ExecutionWitness) (inst : Instruction)
    (h_cycle : Relation.TransGen (sc_rel ew) inst inst) :
    ∃ s, s.isStore = true ∧
      (s = inst ∨ (Relation.TransGen (sc_rel ew) inst s ∧ Relation.TransGen (sc_rel ew) s inst)) := by
  -- We prove by showing: if inst is a load, then either inst reaches a store, or all nodes are loads
  by_cases h_inst_store : inst.isStore = true
  · exact ⟨inst, h_inst_store, Or.inl rfl⟩
  · -- inst is not a store, so it's a load (mem inst on sc_rel)
    -- Trace the cycle to find a store
    -- The first edge from inst is one of: rf (impossible, inst not store), co (impossible),
    -- fr (goes to store), poloc (could stay at loads)
    obtain ⟨next, h_edge, h_rest⟩ := transGen_first_edge' inst inst h_cycle
    cases sc_rel_to_edge_type ew inst next h_edge with
    | rf_edge h_rf =>
      -- rf source is store, but inst is not store - contradiction
      exact absurd (rf_source_is_store ew.aa ew.rf inst next h_rf) h_inst_store
    | co_edge h_co =>
      -- co source is store, but inst is not store - contradiction
      exact absurd (co_source_is_store ew.aa ew.mo inst next h_co) h_inst_store
    | fr_edge h_fr =>
      -- fr goes to a store!
      have h_next_store := fr_target_is_store ew.aa ew.rf ew.mo inst next h_fr
      cases h_rest with
      | inl h_eq =>
        -- next = inst, but next is store and inst is not - contradiction
        exact absurd (h_eq ▸ h_next_store) h_inst_store
      | inr h_path =>
        -- inst → next (store) and next →+ inst
        exact ⟨next, h_next_store, Or.inr ⟨Relation.TransGen.single h_edge, h_path⟩⟩
    | poloc_edge h_poloc =>
      -- poloc: check if next is a store
      have h_next_mem := h_poloc.2.2.2
      rw [isMemInst_iff_load_or_store] at h_next_mem
      cases h_next_mem with
      | inr h_next_store =>
        cases h_rest with
        | inl h_eq => exact absurd (h_eq ▸ h_next_store) h_inst_store
        | inr h_path => exact ⟨next, h_next_store, Or.inr ⟨Relation.TransGen.single h_edge, h_path⟩⟩
      | inl h_next_load =>
        -- next is also a load. We have: inst (load) → next (load) via poloc
        -- And either next = inst (contradiction with po irrefl) or next →+ inst
        cases h_rest with
        | inl h_eq =>
          -- next = inst: single edge poloc cycle inst → inst
          -- poloc gives po, so po inst inst, contradiction
          exact absurd (h_eq ▸ h_poloc.1) (ew.po.irrefl inst)
        | inr h_path =>
          -- next →+ inst: we need to find a store in this path
          -- Key insight: in any sc_rel path, if a node is a store, we're done.
          -- If all nodes are loads, then all edges must be poloc (rf/co source is store,
          -- fr target is store), and we get a po path, hence po cycle, contradiction.
          -- For now, use a simple lemma: any TransGen sc_rel has a store, or gives TransGen po
          -- This is essentially sc_rel_between_loads_is_poloc_path
          -- Actually, we can use: sc_rel cycle starting at load must have a store
          -- by edge type analysis.
          -- Since inst is a load, the outgoing edge inst → next is poloc (we know this)
          -- For the return path next →+ inst:
          --   - If any edge is rf: source is store
          --   - If any edge is co: source is store
          --   - If any edge is fr: target is store
          --   - If all edges are poloc: we get TransGen po next inst, combined with
          --     po inst next from our poloc, giving po cycle on next, contradiction
          -- Let's prove: TransGen sc_rel a b where a is load → either store on path or TransGen po a b
          have h_sc_rel_load_gives_store_or_po : ∀ (a b : Instruction),
              a.isLoad = true → Relation.TransGen (sc_rel ew) a b →
              (∃ s, s.isStore = true ∧ (s = a ∨ Relation.TransGen (sc_rel ew) a s) ∧
                                       (s = b ∨ Relation.TransGen (sc_rel ew) s b)) ∨
              Relation.TransGen ew.po.rel a b := by
            intro a _ h_a_load h_path
            induction h_path with
            | single h_e =>
              -- Single edge a → endpoint. By edge type:
              rename_i endpoint
              cases sc_rel_to_edge_type ew a endpoint h_e with
              | rf_edge h_rf =>
                -- rf source is store, but a is load - contradiction
                exact absurd (rf_source_is_store ew.aa ew.rf a endpoint h_rf) (load_not_store a h_a_load)
              | co_edge h_co =>
                exact absurd (co_source_is_store ew.aa ew.mo a endpoint h_co) (load_not_store a h_a_load)
              | fr_edge h_fr =>
                -- fr target is store
                have h_endpoint_store := fr_target_is_store ew.aa ew.rf ew.mo a endpoint h_fr
                exact Or.inl ⟨endpoint, h_endpoint_store, Or.inr (Relation.TransGen.single h_e), Or.inl rfl⟩
              | poloc_edge h_poloc_ab =>
                exact Or.inr (Relation.TransGen.single h_poloc_ab.1)
            | tail h_rest h_last ih =>
              rename_i mid endpoint
              cases ih with
              | inl h_store =>
                -- Found store on path a →+ mid
                obtain ⟨s, h_s_store, h_from_a, h_to_mid⟩ := h_store
                cases h_to_mid with
                | inl h_eq => exact Or.inl ⟨s, h_s_store, h_from_a, Or.inr (h_eq ▸ Relation.TransGen.single h_last)⟩
                | inr h_s_to_mid =>
                  exact Or.inl ⟨s, h_s_store, h_from_a, Or.inr (Relation.TransGen.tail h_s_to_mid h_last)⟩
              | inr h_po_path =>
                -- No store on a →+ mid, got TransGen po a mid
                -- Now analyze edge mid → endpoint
                cases sc_rel_to_edge_type ew mid endpoint h_last with
                | rf_edge h_rf =>
                  have h_mid_store := rf_source_is_store ew.aa ew.rf mid endpoint h_rf
                  exact Or.inl ⟨mid, h_mid_store, Or.inr h_rest, Or.inr (Relation.TransGen.single h_last)⟩
                | co_edge h_co =>
                  have h_mid_store := co_source_is_store ew.aa ew.mo mid endpoint h_co
                  exact Or.inl ⟨mid, h_mid_store, Or.inr h_rest, Or.inr (Relation.TransGen.single h_last)⟩
                | fr_edge h_fr =>
                  have h_endpoint_store := fr_target_is_store ew.aa ew.rf ew.mo mid endpoint h_fr
                  exact Or.inl ⟨endpoint, h_endpoint_store, Or.inr (Relation.TransGen.tail h_rest h_last), Or.inl rfl⟩
                | poloc_edge h_poloc_mid_endpoint =>
                  exact Or.inr (Relation.TransGen.tail h_po_path h_poloc_mid_endpoint.1)
          -- Apply to h_path : TransGen (sc_rel ew) next inst
          cases h_sc_rel_load_gives_store_or_po next inst h_next_load h_path with
          | inl h_store =>
            obtain ⟨s, h_s_store, h_from_next, h_to_inst⟩ := h_store
            -- Found store s on path next →+ inst
            cases h_from_next with
            | inl h_eq =>
              -- s = next, but next is load - contradiction
              exact absurd (h_eq ▸ h_s_store) (load_not_store next h_next_load)
            | inr h_next_to_s =>
              cases h_to_inst with
              | inl h_eq =>
                -- s = inst, but inst is not store - contradiction
                exact absurd (h_eq ▸ h_s_store) h_inst_store
              | inr h_s_to_inst =>
                -- next →+ s →+ inst, and inst → next (h_edge)
                -- So inst → next →+ s means inst →+ s
                -- And s →+ inst
                have h_inst_to_s : Relation.TransGen (sc_rel ew) inst s :=
                  Relation.TransGen.trans (Relation.TransGen.single h_edge) h_next_to_s
                exact ⟨s, h_s_store, Or.inr ⟨h_inst_to_s, h_s_to_inst⟩⟩
          | inr h_po_path =>
            -- No store on path, got TransGen po next inst
            -- Combined with h_poloc.1 : po inst next, get po cycle
            have h_po_next_next := Relation.TransGen.tail h_po_path h_poloc.1
            have h_po_next := po_transgen_to_po ew.po next next h_po_next_next
            exact absurd h_po_next (ew.po.irrefl next)

/-- Main SC-per-Location proof: acyclic(rf ∪ co ∪ fr ∪ poloc)

    Strategy (following the paper):
    1. Any cycle must contain at least one store (by sc_rel_cycle_has_store)
    2. Starting from any store s, the path s →+ s can be reduced to mo path
       (by sc_rel_stores_transgen_to_mo)
    3. This gives mo s s, contradicting mo acyclicity -/
theorem sc_per_location_acyclic (of : OrderedFunc) (ew : ExecutionWitness)
    (_prog : ProgramExecution)
    (_h_wf : ew.aa.onlyMemInst _prog.allInstructions)
    (h_instOrder : satisfies_InstOrder of ew)
    (h_loadValue : satisfies_LoadValue ew) :
    acyclic (sc_rel ew) := by
  intro inst h_cycle
  -- Step 1: Find a store in the cycle
  obtain ⟨s, h_s_store, h_s_in_cycle⟩ := sc_rel_cycle_has_store ew inst h_cycle
  -- Step 2: Construct cycle at s
  have h_s_cycle : Relation.TransGen (sc_rel ew) s s := by
    cases h_s_in_cycle with
    | inl h_eq => exact h_eq ▸ h_cycle
    | inr h_paths =>
      obtain ⟨h_inst_to_s, h_s_to_inst⟩ := h_paths
      exact Relation.TransGen.trans h_s_to_inst h_inst_to_s
  -- Step 3: Reduce to mo cycle
  have h_mo_cycle := sc_rel_stores_transgen_to_mo of ew h_instOrder h_loadValue
    s s h_s_store h_s_store h_s_cycle
  -- Step 4: Contradiction with mo acyclicity
  exact mo_acyclic ew s h_mo_cycle

end GamI2e
