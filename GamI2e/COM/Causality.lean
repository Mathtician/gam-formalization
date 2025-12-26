/-
COM: Causality Proof Infrastructure

This module contains the main causality proofs showing that TransGen paths
through the causality relation (rfe ∪ co ∪ fr ∪ ppo) between memory
instructions map to mo paths.
-/

import GamI2e.COM.CausalityHelpers

namespace GamI2e

/-- A single causality edge between two mem instructions maps to mo. -/
theorem causality_single_mem_to_mo (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew) (h_loadValue : satisfies_LoadValue ew)
    (i1 i2 : Instruction) (h_i1_mem : i1.isMemInst = true) (h_i2_mem : i2.isMemInst = true)
    (h_edge : (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
               fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) i1 i2) :
    ew.mo.rel i1 i2 := by
  have h := com_contained_in_mo of ew h_instOrder h_loadValue i1 i2 h_i1_mem h_i2_mem
  cases h_edge with
  | inl h123 =>
    cases h123 with
    | inl h12 =>
      cases h12 with
      | inl h_rfe => exact h (Or.inl h_rfe)
      | inr h_co => exact h (Or.inr (Or.inl h_co))
    | inr h_fr => exact h (Or.inr (Or.inr (Or.inl h_fr)))
  | inr h_ppo => exact h (Or.inr (Or.inr (Or.inr h_ppo)))

/-- TransGen causality from non-mem source implies ppo to target.
    If source is non-mem and TransGen causality source target,
    then there exists some intermediate node m such that ppo source m and
    either m = target or TransGen causality m target.

    This follows because the first edge from a non-mem source must be ppo. -/
theorem causality_transgen_from_nonmem_first_ppo (of : OrderedFunc) (ew : ExecutionWitness)
    (source target : Instruction) (h_nonmem : source.isMemInst ≠ true)
    (h_path : Relation.TransGen
      (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
        fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) source target) :
    ∃ m, (ppo[ew.aa,of,ew.po]) source m ∧
         (m = target ∨ Relation.TransGen
           (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
             fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) m target) := by
  have h_first := transGen_first_edge source target h_path
  obtain ⟨m, h_edge, h_rest⟩ := h_first
  refine ⟨m, ?_, h_rest⟩
  -- Show ppo source m from the edge h_edge
  -- The edge is in the union, so case split
  cases h_edge with
  | inl h =>
    cases h with
    | inl h =>
      cases h with
      | inl h_rfe => exact absurd (rfe_mem_source ew source m h_rfe) h_nonmem
      | inr h_co => exact absurd (co_mem_source ew source m h_co) h_nonmem
    | inr h_fr => exact absurd (fr_mem_source ew source m h_fr) h_nonmem
  | inr h_ppo => exact h_ppo

/-- Key lemma: A single causality edge from a non-mem source must be ppo.
    rfe/co/fr all require memory instruction sources. -/
theorem causality_edge_from_nonmem_is_ppo (of : OrderedFunc) (ew : ExecutionWitness)
    (i1 i2 : Instruction) (h_i1_nonmem : i1.isMemInst ≠ true)
    (h_edge : (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
               fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) i1 i2) :
    (ppo[ew.aa,of,ew.po]) i1 i2 := by
  cases h_edge with
  | inl h =>
    cases h with
    | inl h =>
      cases h with
      | inl h_rfe => exact absurd (rfe_mem_source ew i1 i2 h_rfe) h_i1_nonmem
      | inr h_co => exact absurd (co_mem_source ew i1 i2 h_co) h_i1_nonmem
    | inr h_fr => exact absurd (fr_mem_source ew i1 i2 h_fr) h_i1_nonmem
  | inr h_ppo => exact h_ppo

/-- Key lemma: A single causality edge to a non-mem target must be ppo.
    rfe/co/fr all require memory instruction targets. -/
theorem causality_edge_to_nonmem_is_ppo (of : OrderedFunc) (ew : ExecutionWitness)
    (i1 i2 : Instruction) (h_i2_nonmem : i2.isMemInst ≠ true)
    (h_edge : (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
               fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) i1 i2) :
    (ppo[ew.aa,of,ew.po]) i1 i2 := by
  cases h_edge with
  | inl h =>
    cases h with
    | inl h =>
      cases h with
      | inl h_rfe => exact absurd (rfe_mem_target ew i1 i2 h_rfe) h_i2_nonmem
      | inr h_co => exact absurd (co_mem_target ew i1 i2 h_co) h_i2_nonmem
    | inr h_fr => exact absurd (fr_mem_target ew i1 i2 h_fr) h_i2_nonmem
  | inr h_ppo => exact h_ppo

/-- Key lemma: If ALL nodes in a causality cycle are non-mem, then every edge is ppo.
    Therefore the cycle reduces to a ppo cycle, contradicting ppo_irrefl.

    This is proven by induction: for each edge in TransGen, if both endpoints are non-mem,
    the edge must be ppo (since rfe/co/fr require mem endpoints).

    Note: We use a generalized statement for the induction to work properly. -/
theorem causality_all_nonmem_is_ppo (of : OrderedFunc) (ew : ExecutionWitness)
    (a b : Instruction)
    (h_path : Relation.TransGen
      (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
        fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a b)
    (h_a_nonmem : a.isMemInst ≠ true)
    (h_b_nonmem : b.isMemInst ≠ true)
    (h_all_nonmem : ∀ x, Relation.TransGen
      (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
        fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a x →
      x.isMemInst ≠ true) :
    (ppo[ew.aa,of,ew.po]) a b := by
  -- Use induction on h_path. The key is that the "all_nonmem" predicate propagates.
  induction h_path with
  | single h_edge =>
    -- Single edge: a is non-mem, so edge must be ppo
    exact causality_edge_from_nonmem_is_ppo of ew a _ h_a_nonmem h_edge
  | tail h_rest h_last ih =>
    -- Path: a →+ mid → c where mid is the intermediate (b✝), c is final (c✝)
    -- h_rest : TransGen a mid, h_last : edge mid c
    -- ih : mid.isMemInst ≠ true → ppo a mid
    rename_i mid c
    -- mid is non-mem (by h_all_nonmem applied to h_rest)
    have h_mid_nonmem : mid.isMemInst ≠ true := h_all_nonmem mid h_rest
    -- Last edge mid → c: mid is non-mem, so ppo mid c
    have h_ppo_mid_c := causality_edge_from_nonmem_is_ppo of ew mid c h_mid_nonmem h_last
    -- For ppo a mid, use the induction hypothesis
    have h_ppo_a_mid : (ppo[ew.aa,of,ew.po]) a mid := ih h_mid_nonmem
    exact ppo_trans ew.aa of ew.po a mid c h_ppo_a_mid h_ppo_mid_c

/-- Helper: Given a path from NON-MEM source to NON-MEM target, either:
    - All nodes are non-mem → return ppo source target
    - Some node is mem → return that node with paths to decompose

    This handles the "m is non-mem" case in the Causality proof. -/
theorem causality_path_nonmem_endpoints (of : OrderedFunc) (ew : ExecutionWitness)
    (_h_instOrder : satisfies_InstOrder of ew) (_h_loadValue : satisfies_LoadValue ew)
    (source : Instruction)
    (h_source_nonmem : source.isMemInst ≠ true)
    {endpoint : Instruction}
    (h_endpoint_nonmem : endpoint.isMemInst ≠ true)
    (h_path : Relation.TransGen
      (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
        fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) source endpoint) :
    (ppo[ew.aa,of,ew.po]) source endpoint ∨
    (∃ n, n.isMemInst = true ∧
          Relation.TransGen (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
                              fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) source n ∧
          Relation.TransGen (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
                              fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) n endpoint) := by
  -- Induction on h_path, tracking whether we've found a mem node
  induction h_path with
  | single h_edge =>
    -- Single edge source → endpoint, source is non-mem, so edge is ppo
    have h_ppo := causality_edge_from_nonmem_is_ppo of ew source _ h_source_nonmem h_edge
    exact Or.inl h_ppo
  | tail h_rest h_last ih =>
    rename_i mid endpoint'
    by_cases h_mid_mem : mid.isMemInst = true
    · -- mid is mem: found our witness!
      -- Paths: source →+ mid (h_rest), mid → endpoint' (h_last as single edge)
      right
      exact ⟨mid, h_mid_mem, h_rest, Relation.TransGen.single h_last⟩
    · -- mid is non-mem: recurse
      have h_mid_nonmem : mid.isMemInst ≠ true := h_mid_mem
      cases ih h_mid_nonmem with
      | inl h_ppo_source_mid =>
        -- All nodes source →+ mid are non-mem, got ppo source mid
        -- Last edge mid → endpoint': mid is non-mem, so ppo mid endpoint'
        have h_ppo_mid_endpoint := causality_edge_from_nonmem_is_ppo of ew mid _ h_mid_nonmem h_last
        left
        exact ppo_trans ew.aa of ew.po source mid _ h_ppo_source_mid h_ppo_mid_endpoint
      | inr h_exists =>
        -- Found mem node n on path source →+ mid
        obtain ⟨n, h_n_mem, h_trans_source_n, h_trans_n_mid⟩ := h_exists
        -- Extend path n →+ mid to n →+ endpoint'
        have h_trans_n_endpoint := Relation.TransGen.tail h_trans_n_mid h_last
        right
        exact ⟨n, h_n_mem, h_trans_source_n, h_trans_n_endpoint⟩

/-- Helper: Given a path a →+ b where b is non-mem, find the last mem node m in the path
    and show ppo m b. Returns (m, TransGen a m or a = m, ppo m b).

    The key insight: edges INTO non-mem nodes must be ppo (rfe/co/fr require mem targets).
    So we trace backwards from b until we find a mem node. -/
theorem causality_last_mem_before_nonmem (of : OrderedFunc) (ew : ExecutionWitness)
    (a : Instruction) (h_a_mem : a.isMemInst = true)
    (b : Instruction) (h_b_nonmem : b.isMemInst ≠ true)
    (h_path : Relation.TransGen
      (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
        fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a b) :
    ∃ m, m.isMemInst = true ∧
         (a = m ∨ Relation.TransGen
           (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
             fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a m) ∧
         (ppo[ew.aa,of,ew.po]) m b := by
  -- Note: induction creates new variables; h_b_nonmem refers to the current endpoint
  induction h_path with
  | single h_edge =>
    -- Single edge a → endpoint, where a is mem and endpoint is non-mem
    have h_ppo := causality_edge_to_nonmem_is_ppo of ew a _ h_b_nonmem h_edge
    exact ⟨a, h_a_mem, Or.inl rfl, h_ppo⟩
  | tail h_rest h_last ih =>
    -- Path a →+ mid → endpoint, where endpoint is non-mem
    -- Rename: b✝ is mid, c✝ is endpoint
    rename_i mid endpoint
    -- ih takes h_mid_nonmem and gives existence of m with ppo m mid
    by_cases h_mid_mem : mid.isMemInst = true
    · -- mid is mem: mid is our answer
      have h_ppo := causality_edge_to_nonmem_is_ppo of ew mid endpoint h_b_nonmem h_last
      exact ⟨mid, h_mid_mem, Or.inr h_rest, h_ppo⟩
    · -- mid is non-mem: recurse to find last mem before mid
      have h_mid_nonmem : mid.isMemInst ≠ true := h_mid_mem
      obtain ⟨m, h_m_mem, h_path_a_m, h_ppo_m_mid⟩ := ih h_mid_nonmem
      -- We have ppo m mid and need ppo m endpoint
      -- The edge mid → endpoint is ppo (since endpoint is non-mem)
      have h_ppo_mid_endpoint := causality_edge_to_nonmem_is_ppo of ew mid endpoint h_b_nonmem h_last
      have h_ppo_m_endpoint := ppo_trans ew.aa of ew.po m mid endpoint h_ppo_m_mid h_ppo_mid_endpoint
      exact ⟨m, h_m_mem, h_path_a_m, h_ppo_m_endpoint⟩

/-- Length of a TransGen path (as a proposition with a witness) -/
private inductive TransGenLen {α : Type} (r : α → α → Prop) : α → α → Nat → Prop
  | single {a b : α} : r a b → TransGenLen r a b 1
  | tail {a b c : α} {n : Nat} : TransGenLen r a b n → r b c → TransGenLen r a c (n + 1)

/-- Every TransGen path has some length -/
private theorem transGen_has_length {α : Type} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) : ∃ n, TransGenLen r a b n := by
  induction h with
  | single h_edge => exact ⟨1, TransGenLen.single h_edge⟩
  | tail _ h_last ih =>
    obtain ⟨n, h_len⟩ := ih
    exact ⟨n + 1, TransGenLen.tail h_len h_last⟩

/-- A TransGenLen witness implies TransGen -/
private theorem transGenLen_to_transGen {α : Type} {r : α → α → Prop} {a b : α} {n : Nat}
    (h : TransGenLen r a b n) : Relation.TransGen r a b := by
  induction h with
  | single h_edge => exact Relation.TransGen.single h_edge
  | tail _ h_last ih => exact Relation.TransGen.tail ih h_last

/-- Helper: if path a →len b and b → c, then path a →len+1 c -/
private theorem transGenLen_extend {α : Type} {r : α → α → Prop} {a b c : α} {n : Nat}
    (h_path : TransGenLen r a b n) (h_edge : r b c) : TransGenLen r a c (n + 1) :=
  TransGenLen.tail h_path h_edge

/-- Helper for causality_last_mem_before_nonmem: the returned path has smaller length -/
private theorem causality_last_mem_before_nonmem_len (of : OrderedFunc) (ew : ExecutionWitness)
    (a : Instruction) (h_a_mem : a.isMemInst = true)
    {n : Nat} {endpoint : Instruction}
    (h_endpoint_nonmem : endpoint.isMemInst ≠ true)
    (h_path : TransGenLen
      (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
        fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a endpoint n) :
    ∃ m, m.isMemInst = true ∧
         (a = m ∨ ∃ k, k < n ∧ TransGenLen
           (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
             fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a m k) ∧
         (ppo[ew.aa,of,ew.po]) m endpoint := by
  induction h_path with
  | single h_edge =>
    -- Single edge a → endpoint, where a is mem and endpoint is non-mem
    have h_ppo := causality_edge_to_nonmem_is_ppo of ew a _ h_endpoint_nonmem h_edge
    exact ⟨a, h_a_mem, Or.inl rfl, h_ppo⟩
  | tail h_rest h_last ih =>
    -- Path a →n mid → endpoint' (n+1 total), where endpoint' is non-mem
    rename_i mid endpoint' n_rest
    by_cases h_mid_mem : mid.isMemInst = true
    · -- mid is mem: mid is our answer
      have h_ppo := causality_edge_to_nonmem_is_ppo of ew mid _ h_endpoint_nonmem h_last
      exact ⟨mid, h_mid_mem, Or.inr ⟨n_rest, Nat.lt_succ_self n_rest, h_rest⟩, h_ppo⟩
    · -- mid is non-mem: recurse to find last mem before mid
      have h_mid_nonmem : mid.isMemInst ≠ true := h_mid_mem
      obtain ⟨m, h_m_mem, h_path_a_m, h_ppo_m_mid⟩ := ih h_mid_nonmem
      -- The edge mid → endpoint' is ppo (since endpoint' is non-mem)
      have h_ppo_mid_endpoint := causality_edge_to_nonmem_is_ppo of ew mid _ h_endpoint_nonmem h_last
      have h_ppo_m_endpoint := ppo_trans ew.aa of ew.po m mid _ h_ppo_m_mid h_ppo_mid_endpoint
      cases h_path_a_m with
      | inl h_eq => exact ⟨m, h_m_mem, Or.inl h_eq, h_ppo_m_endpoint⟩
      | inr h_exists =>
        obtain ⟨k, h_k_lt, h_path_k⟩ := h_exists
        exact ⟨m, h_m_mem, Or.inr ⟨k, Nat.lt_trans h_k_lt (Nat.lt_succ_self n_rest), h_path_k⟩, h_ppo_m_endpoint⟩

/-- Helper: strong induction on path length for causality_transgen_mem_to_mo -/
private theorem causality_transgen_mem_to_mo_len (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew) (h_loadValue : satisfies_LoadValue ew)
    (n : Nat) : ∀ (a : Instruction) (_h_a_mem : a.isMemInst = true)
                 (b : Instruction) (_h_b_mem : b.isMemInst = true)
                 (_h_path : TransGenLen
                   (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
                     fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a b n),
               Relation.TransGen ew.mo.rel a b := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a h_a_mem b h_b_mem h_path
    cases h_path with
    | single h_edge =>
      exact Relation.TransGen.single (causality_single_mem_to_mo of ew h_instOrder h_loadValue a b h_a_mem h_b_mem h_edge)
    | tail h_rest h_last =>
      rename_i mid n_rest
      by_cases h_mid_mem : mid.isMemInst = true
      · -- mid is mem: straightforward via IH
        have h_lt : n_rest < n_rest + 1 := Nat.lt_succ_self n_rest
        have h_mo_a_mid := ih n_rest h_lt a h_a_mem mid h_mid_mem h_rest
        have h_mo_mid_b := causality_single_mem_to_mo of ew h_instOrder h_loadValue mid b h_mid_mem h_b_mem h_last
        exact Relation.TransGen.tail h_mo_a_mid h_mo_mid_b
      · -- mid is non-mem: find last mem node m before mid
        have h_mid_nonmem : mid.isMemInst ≠ true := h_mid_mem
        obtain ⟨m, h_m_mem, h_path_a_m, h_ppo_m_mid⟩ :=
          causality_last_mem_before_nonmem_len of ew a h_a_mem h_mid_nonmem h_rest
        -- Compose ppo m mid with the edge mid → b
        have h_ppo_mid_b := causality_edge_from_nonmem_is_ppo of ew mid b h_mid_nonmem h_last
        have h_ppo_m_b := ppo_trans ew.aa of ew.po m mid b h_ppo_m_mid h_ppo_mid_b
        -- ppo m b between mem nodes maps to mo
        have h_mo_m_b := com_contained_in_mo of ew h_instOrder h_loadValue m b h_m_mem h_b_mem
          (Or.inr (Or.inr (Or.inr h_ppo_m_b)))
        -- Connect: either a = m or TransGen a m with smaller length
        cases h_path_a_m with
        | inl h_eq => exact h_eq ▸ Relation.TransGen.single h_mo_m_b
        | inr h_exists =>
          obtain ⟨k, h_k_lt, h_path_k⟩ := h_exists
          have h_k_lt' : k < n_rest + 1 := Nat.lt_trans h_k_lt (Nat.lt_succ_self n_rest)
          have h_mo_a_m := ih k h_k_lt' a h_a_mem m h_m_mem h_path_k
          exact Relation.TransGen.tail h_mo_a_m h_mo_m_b

/-- A causality TransGen path between two mem instructions maps to an mo TransGen path.

    Key insight: when the path goes through non-mem nodes, all edges to/from non-mem
    nodes must be ppo (since rfe/co/fr require mem endpoints). We find the last mem
    node before any non-mem segment and compose ppo edges to get a single ppo between
    mem nodes, which maps to mo. -/
theorem causality_transgen_mem_to_mo (of : OrderedFunc) (ew : ExecutionWitness)
    (h_instOrder : satisfies_InstOrder of ew) (h_loadValue : satisfies_LoadValue ew)
    (a : Instruction) (h_a_mem : a.isMemInst = true)
    (b : Instruction) (h_b_mem : b.isMemInst = true)
    (h_path : Relation.TransGen
      (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
        fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) a b) :
    Relation.TransGen ew.mo.rel a b := by
  -- Convert TransGen to TransGenLen, then apply the length-indexed theorem
  obtain ⟨n, h_len⟩ := transGen_has_length h_path
  exact causality_transgen_mem_to_mo_len of ew h_instOrder h_loadValue n a h_a_mem b h_b_mem h_len

end GamI2e
