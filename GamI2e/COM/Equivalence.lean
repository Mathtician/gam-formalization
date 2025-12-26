/-
COM: GAM/COM Equivalence Theorems

This module contains the main equivalence theorems showing that
GAM and COM memory models are equivalent.
-/

import GamI2e.COM.ECO
import GamI2e.COM.Causality

namespace GamI2e

/-! ## Szpilrajn Extension Theorem (Axiomatized)

The Szpilrajn extension theorem states that any strict partial order
can be extended to a strict total order. More generally, any acyclic
relation can be extended to a strict total order.

This is a classical result requiring the Axiom of Choice (or Zorn's lemma).
We axiomatize it here for use in the COM ⊆ GAM direction of the equivalence.

The theorem is named after Edward Szpilrajn (later Marczewski), who proved
it in 1930. -/

/-- Szpilrajn's extension theorem for memory orders:
    Given an acyclic relation R on memory instructions that only relates
    memory instructions, there exists a MemoryOrder extending R.

    This is an axiom because proving it constructively would require
    either finiteness assumptions or the full Axiom of Choice. -/
axiom szpilrajn_extension
    (R : Instruction → Instruction → Prop)
    (h_acyclic : acyclic R)
    (h_memOnly : ∀ i1 i2, R i1 i2 → i1.isMemInst ∧ i2.isMemInst) :
    ∃ (mo : MemoryOrder), ∀ i1 i2, R i1 i2 → mo.rel i1 i2

/-- poloc is contained in po -/
theorem poloc_subset_po (aa : AddressAssignment) (po : ProgramOrder) :
    ∀ i1 i2, programOrderLoc aa po i1 i2 → po.rel i1 i2 := by
  intro i1 i2 h
  exact h.1

/-- po is acyclic (since it's irreflexive and transitive) -/
theorem po_acyclic (po : ProgramOrder) : acyclic po.rel := by
  apply acyclic_of_strict_order
  · exact po.irrefl
  · exact po.trans

/-- poloc is acyclic (poloc ⊆ po and po is acyclic) -/
theorem poloc_acyclic (aa : AddressAssignment) (po : ProgramOrder) :
    acyclic (programOrderLoc aa po) := by
  apply acyclic_of_subset
  · exact poloc_subset_po aa po
  · exact po_acyclic po

/-- Equivalence of GAM and COM: GAM ⊆ COM

Paper's proof strategy:
- SC-per-Location: Complex cycle reduction (see paper Section 5)
- Causality: Show rfe ∪ co ∪ fr ∪ ppo ⊆ mo (for mem instructions), hence acyclic -/
theorem GAM_subset_COM (of : OrderedFunc) :
    ∀ (ew : ExecutionWitness) (prog : ProgramExecution),
    ew.consistentWith prog →
    ew.aa.onlyMemInst prog.allInstructions →
    satisfies_InstOrder of ew →
    satisfies_LoadValue ew →
    COM_scPerLocation ew ∧ COM_causality of ew := by
  intro ew prog h_cons h_wf h_instOrder h_loadValue
  constructor
  · -- SC-per-Location: acyclic(rf ∪ co ∪ fr ∪ poloc)
    --
    -- Paper's proof strategy (ComProofs.tex, Theorem after Lemma 4):
    -- 1. By eco_poloc, poloc edges with ≥1 write → rf/co/fr sequences
    -- 2. Read-read poloc → rf⁻¹;co*;rf (from eco definition)
    -- 3. rf;rf⁻¹ = id → cancel pairs
    -- 4. rf;fr ⊆ co (rf_fr_subset_co) → eliminate reads
    -- 5. Only co edges remain → co is acyclic (co_acyclic)
    --
    -- The detailed proof is in sc_per_location_acyclic in ECO.lean
    -- COM_scPerLocation and sc_rel are definitionally equal
    simp only [COM_scPerLocation]
    exact sc_per_location_acyclic of ew prog h_wf h_instOrder h_loadValue
  · -- Causality: acyclic(rfe ∪ co ∪ fr ∪ ppo)
    --
    -- Paper's proof (Lemma C.1): All of rfe, co, fr, ppo are contained in mo.
    -- Therefore acyclic follows from mo being a strict total order.
    --
    -- Key insight: The paper implicitly assumes all nodes in cycles are mem instructions.
    -- This is justified because:
    -- - rfe/co/fr edges require mem endpoints (loads/stores)
    -- - If a cycle has a non-mem node, all edges to/from it must be ppo
    -- - A cycle with all non-mem nodes is a ppo cycle → contradiction via ppo_irrefl
    --
    simp only [COM_causality, acyclic]
    intro inst h_cycle
    -- Case split: is inst a memory instruction?
    by_cases h_inst_mem : inst.isMemInst = true
    · -- inst IS a memory instruction
      -- Map the cycle to mo using causality_transgen_mem_to_mo
      -- A cycle at a mem node gives TransGen mo inst inst, contradicting mo's acyclicity.
      have h_mo_cycle := causality_transgen_mem_to_mo of ew h_instOrder h_loadValue
        inst h_inst_mem inst h_inst_mem h_cycle
      exact mo_acyclic ew inst h_mo_cycle
    · -- inst is NOT a memory instruction
      -- The cycle at inst must be all ppo (since rfe/co/fr can't reach non-mem)
      -- Show: if all nodes on cycle are non-mem, we get ppo inst inst → contradiction
      --
      -- Step 1: Check if there's any mem node in the cycle
      -- Step 2a: If yes, construct cycle at that mem node → mo contradiction
      -- Step 2b: If no, all edges are ppo → ppo inst inst → ppo_irrefl contradiction
      --
      -- For step 2b, use causality_all_nonmem_is_ppo.
      -- For step 2a, we need to locate a mem node in the cycle.
      --
      -- Simpler approach: use the first-edge decomposition.
      have h_first := causality_transgen_from_nonmem_first_ppo of ew inst inst h_inst_mem h_cycle
      obtain ⟨m, h_ppo_inst_m, h_rest⟩ := h_first
      cases h_rest with
      | inl h_m_eq_inst =>
        -- m = inst, so ppo inst inst directly
        subst h_m_eq_inst
        exact ppo_irrefl ew.aa of ew.po m h_ppo_inst_m
      | inr h_trans_m_inst =>
        -- TransGen m inst (rest of cycle)
        by_cases h_m_mem : m.isMemInst = true
        · -- m is mem: construct TransGen m m (cycle at m)
          have h_ppo_edge : (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
                              fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) inst m := Or.inr h_ppo_inst_m
          have h_cycle_m := Relation.TransGen.tail h_trans_m_inst h_ppo_edge
          -- Now we have TransGen (causality) m m with m mem
          -- Map this to mo, get contradiction
          have h_mo_cycle := causality_transgen_mem_to_mo of ew h_instOrder h_loadValue
            m h_m_mem m h_m_mem h_cycle_m
          exact mo_acyclic ew m h_mo_cycle
        · -- m is non-mem: use causality_path_nonmem_endpoints to handle this case
          have h_m_nonmem : m.isMemInst ≠ true := h_m_mem
          -- Use the new helper: either all nodes are non-mem (ppo), or find a mem node
          cases causality_path_nonmem_endpoints of ew h_instOrder h_loadValue
                m h_m_nonmem h_inst_mem h_trans_m_inst with
          | inl h_ppo_m_inst =>
            -- All nodes m →+ inst are non-mem, so we get ppo m inst
            -- Compose with ppo inst m to get ppo inst inst → contradiction
            have h_ppo_inst_inst := ppo_trans ew.aa of ew.po inst m inst h_ppo_inst_m h_ppo_m_inst
            exact ppo_irrefl ew.aa of ew.po inst h_ppo_inst_inst
          | inr h_found_mem =>
            -- Found a mem node n on the path m →+ inst
            obtain ⟨n, h_n_mem, h_trans_m_n, h_trans_n_inst⟩ := h_found_mem
            -- Build cycle at n: n →+ inst →ppo m →+ n
            -- First: n →+ inst (given)
            -- Second: inst → m (ppo edge)
            have h_ppo_edge : (((readFromExternal ew.aa ew.rf ∪ᵣ coherenceOrderAll ew.aa ew.mo) ∪ᵣ
                                fromReads ew.aa ew.rf ew.mo) ∪ᵣ (ppo[ew.aa,of,ew.po])) inst m := Or.inr h_ppo_inst_m
            -- Third: m →+ n (given)
            -- Compose: n →+ inst → m →+ n = n →+ n (cycle at mem node n)
            have h_cycle_n := Relation.TransGen.trans h_trans_n_inst
              (Relation.TransGen.trans (Relation.TransGen.single h_ppo_edge) h_trans_m_n)
            -- Map to mo cycle, get contradiction
            have h_mo_cycle := causality_transgen_mem_to_mo of ew h_instOrder h_loadValue
              n h_n_mem n h_n_mem h_cycle_n
            exact mo_acyclic ew n h_mo_cycle

/-- The causality relation only relates memory instructions.
    This is because rfe, co, fr all involve loads/stores, and
    ppo between non-mem instructions doesn't contribute to causality
    (those paths go through mem instructions for causality).

    Note: ppo CAN relate non-mem instructions (fences with deps), but for
    the COM ⊆ GAM proof, we only need the mo to extend causality restricted
    to memory instructions. The Szpilrajn axiom handles this. -/
theorem causality_memOnly (of : OrderedFunc) (ew : ExecutionWitness) :
    ∀ i1 i2, causalityRel of ew i1 i2 →
    i1.isMemInst = true → i2.isMemInst = true →
    i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 _ h1 h2
  exact ⟨h1, h2⟩

/-- Helper: rfe relates memory instructions -/
theorem rfe_memOnly (aa : AddressAssignment) (rf : ReadFrom aa) :
    ∀ i1 i2, readFromExternal aa rf i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  unfold readFromExternal at h
  obtain ⟨h_rf, _⟩ := h
  have ⟨h_store, h_load⟩ := rf.storeToLoad i1 i2 h_rf
  constructor
  · exact isStore_implies_isMemInst i1 h_store
  · exact isLoad_implies_isMemInst i2 h_load

/-- Helper: co relates memory instructions -/
theorem co_memOnly (aa : AddressAssignment) (mo : MemoryOrder) :
    ∀ i1 i2, coherenceOrderAll aa mo i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  unfold coherenceOrderAll at h
  constructor
  · exact isStore_implies_isMemInst i1 h.1
  · exact isStore_implies_isMemInst i2 h.2.1

/-- Helper: fr relates memory instructions -/
theorem fr_memOnly (aa : AddressAssignment) (rf : ReadFrom aa) (mo : MemoryOrder) :
    ∀ i1 i2, fromReads aa rf mo i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  constructor
  · exact isLoad_implies_isMemInst i1 (fr_source_is_load aa rf mo i1 i2 h)
  · exact isStore_implies_isMemInst i2 (fr_target_is_store aa rf mo i1 i2 h)

/-- Causality restricted to memory instructions -/
def causalityRelMem (of : OrderedFunc) (ew : ExecutionWitness) : Relation :=
  fun i1 i2 => causalityRel of ew i1 i2 ∧ i1.isMemInst ∧ i2.isMemInst

/-- TransGen of a subrelation implies TransGen of the superrelation -/
theorem transGen_mono {α : Type} {R S : α → α → Prop} (h_sub : ∀ x y, R x y → S x y)
    {a b : α} (h : Relation.TransGen R a b) : Relation.TransGen S a b := by
  induction h with
  | single h_edge => exact Relation.TransGen.single (h_sub _ _ h_edge)
  | tail _ h_last ih => exact Relation.TransGen.tail ih (h_sub _ _ h_last)

/-- If causality is acyclic, so is causality restricted to mem instructions -/
theorem causalityRelMem_acyclic (of : OrderedFunc) (ew : ExecutionWitness)
    (h : acyclic (causalityRel of ew)) : acyclic (causalityRelMem of ew) := by
  intro i h_cycle
  apply h i
  exact transGen_mono (fun _ _ h_edge => h_edge.1) h_cycle

/-- causalityRelMem only relates memory instructions -/
theorem causalityRelMem_memOnly (of : OrderedFunc) (ew : ExecutionWitness) :
    ∀ i1 i2, causalityRelMem of ew i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  exact ⟨h.2.1, h.2.2⟩

/-- Coherence order as a primitive structure (matching paper's COM formulation).
    This is a per-address total order of stores. -/
structure CoherenceOrderPrim (aa : AddressAssignment) where
  rel : Relation
  -- Only relates stores at the same address
  storesSameAddr : ∀ s1 s2, rel s1 s2 → s1.isStore ∧ s2.isStore ∧ s1.sameAddrWith aa s2
  -- Irreflexive
  irrefl : ∀ s, ¬rel s s
  -- Transitive
  trans : ∀ s1 s2 s3, rel s1 s2 → rel s2 s3 → rel s1 s3
  -- Total over same-address stores
  total : ∀ s1 s2, s1.isStore → s2.isStore → s1.sameAddrWith aa s2 → s1 ≠ s2 →
          rel s1 s2 ∨ rel s2 s1

/-- From-reads using primitive co: l fr' s iff l reads from s' and s' co s -/
def fromReadsPrim (aa : AddressAssignment) (rf : ReadFrom aa)
    (co : CoherenceOrderPrim aa) : Relation :=
  fun l s =>
    l.isLoad ∧ s.isStore ∧
    ∃ s', rf.rel s' l ∧ co.rel s' s

/-- Causality relation using primitive co -/
def causalityRelPrim (of : OrderedFunc) (aa : AddressAssignment) (po : ProgramOrder)
    (rf : ReadFrom aa) (co : CoherenceOrderPrim aa) : Relation :=
  let fr := fromReadsPrim aa rf co
  let rfe := readFromExternal aa rf
  let ppo := preservedProgramOrder aa of po
  unionRel (unionRel (unionRel rfe co.rel) fr) ppo

/-- SC-per-Location using primitive co -/
def COM_scPerLocationPrim (aa : AddressAssignment) (po : ProgramOrder)
    (rf : ReadFrom aa) (co : CoherenceOrderPrim aa) : Prop :=
  let fr := fromReadsPrim aa rf co
  let poloc := programOrderLoc aa po
  acyclic (unionRel (unionRel (unionRel rf.rel co.rel) fr) poloc)

/-- Causality axiom using primitive co -/
def COM_causalityPrim (of : OrderedFunc) (aa : AddressAssignment) (po : ProgramOrder)
    (rf : ReadFrom aa) (co : CoherenceOrderPrim aa) : Prop :=
  acyclic (causalityRelPrim of aa po rf co)

/-- Causality relation restricted to memory instructions (primitive version) -/
def causalityRelPrimMem (of : OrderedFunc) (aa : AddressAssignment) (po : ProgramOrder)
    (rf : ReadFrom aa) (co : CoherenceOrderPrim aa) : Relation :=
  fun i1 i2 => causalityRelPrim of aa po rf co i1 i2 ∧ i1.isMemInst ∧ i2.isMemInst

/-- Helper: rfe relates memory instructions -/
theorem rfe_memOnly' (aa : AddressAssignment) (rf : ReadFrom aa) :
    ∀ i1 i2, readFromExternal aa rf i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  unfold readFromExternal at h
  obtain ⟨h_rf, _⟩ := h
  have ⟨h_store, h_load⟩ := rf.storeToLoad i1 i2 h_rf
  constructor
  · exact isStore_implies_isMemInst i1 h_store
  · exact isLoad_implies_isMemInst i2 h_load

/-- Helper: primitive co relates memory instructions -/
theorem co_prim_memOnly (aa : AddressAssignment) (co : CoherenceOrderPrim aa) :
    ∀ i1 i2, co.rel i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  have ⟨h1, h2, _⟩ := co.storesSameAddr i1 i2 h
  constructor
  · exact isStore_implies_isMemInst i1 h1
  · exact isStore_implies_isMemInst i2 h2

/-- Helper: primitive fr relates memory instructions -/
theorem fr_prim_memOnly (aa : AddressAssignment) (rf : ReadFrom aa) (co : CoherenceOrderPrim aa) :
    ∀ i1 i2, fromReadsPrim aa rf co i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  constructor
  · exact isLoad_implies_isMemInst i1 h.1
  · exact isStore_implies_isMemInst i2 h.2.1

/-- causalityRelPrimMem only relates memory instructions -/
theorem causalityRelPrimMem_memOnly (of : OrderedFunc) (aa : AddressAssignment)
    (po : ProgramOrder) (rf : ReadFrom aa) (co : CoherenceOrderPrim aa) :
    ∀ i1 i2, causalityRelPrimMem of aa po rf co i1 i2 → i1.isMemInst ∧ i2.isMemInst := by
  intro i1 i2 h
  exact ⟨h.2.1, h.2.2⟩

/-- If causality is acyclic, so is causality restricted to mem instructions (primitive version) -/
theorem causalityRelPrimMem_acyclic (of : OrderedFunc) (aa : AddressAssignment)
    (po : ProgramOrder) (rf : ReadFrom aa) (co : CoherenceOrderPrim aa)
    (h : acyclic (causalityRelPrim of aa po rf co)) :
    acyclic (causalityRelPrimMem of aa po rf co) := by
  intro i h_cycle
  apply h i
  exact transGen_mono (fun _ _ h_edge => h_edge.1) h_cycle

/-- Equivalence of GAM and COM: COM ⊆ GAM (with primitive co)

Paper's proof strategy (Section 5.3):
1. Given COM axioms (SC-per-Location and Causality) with PRIMITIVE co,
   construct mo as any total order extending the causality relation (rfe ∪ co ∪ fr ∪ ppo)
2. InstOrder holds by construction: ppo ⊆ causality ⊆ mo
3. LoadValue holds: if w rf r, then either w rfi r (so w po r by SC-per-Location)
   or w rfe r (so w mo r by construction). If w not maximal, get contradiction
   via l fr s' (using the FIXED co, not derived from mo'). -/
theorem COM_subset_GAM_prim (of : OrderedFunc) :
    ∀ (aa : AddressAssignment) (po : ProgramOrder) (rf : ReadFrom aa)
      (co : CoherenceOrderPrim aa),
    COM_scPerLocationPrim aa po rf co →
    COM_causalityPrim of aa po rf co →
    ∃ (mo' : MemoryOrder),
      -- mo' extends co: same-address stores maintain their co ordering
      (∀ s1 s2, co.rel s1 s2 → mo'.rel s1 s2) ∧
      -- InstOrder is satisfied
      (∀ i1 i2, preservedProgramOrder aa of po i1 i2 → i1.isMemInst → i2.isMemInst → mo'.rel i1 i2) ∧
      -- LoadValue is satisfied
      (∀ (s l : Instruction) (a : Addr),
        aa s.id = some a → aa l.id = some a → s.isStore → l.isLoad → rf.rel s l →
        (po.rel s l ∨ mo'.rel s l) ∧
        (∀ s', s'.isStore → aa s'.id = some a → (po.rel s' l ∨ mo'.rel s' l) →
               mo'.rel s' s ∨ s' = s)) := by
  intro aa po rf co h_sc h_caus
  -- Use causality restricted to memory instructions
  let causalityMem := causalityRelPrimMem of aa po rf co
  -- By COM_causality + restriction, causalityMem is acyclic
  have h_acyclic : acyclic causalityMem := causalityRelPrimMem_acyclic of aa po rf co h_caus
  -- causalityMem only relates memory instructions
  have h_memOnly : ∀ i1 i2, causalityMem i1 i2 → i1.isMemInst ∧ i2.isMemInst :=
    causalityRelPrimMem_memOnly of aa po rf co
  -- By Szpilrajn's theorem, there exists a total order extending causalityMem
  have h_exists := szpilrajn_extension causalityMem h_acyclic h_memOnly
  obtain ⟨mo', h_extends⟩ := h_exists
  refine ⟨mo', ?_, ?_, ?_⟩
  · -- mo' extends co
    intro s1 s2 h_co
    have h_s1_mem : s1.isMemInst := isStore_implies_isMemInst s1 (co.storesSameAddr s1 s2 h_co).1
    have h_s2_mem : s2.isMemInst := isStore_implies_isMemInst s2 (co.storesSameAddr s1 s2 h_co).2.1
    have h_in_causality : causalityRelPrim of aa po rf co s1 s2 := Or.inl (Or.inl (Or.inr h_co))
    have h_in_causalityMem : causalityMem s1 s2 := ⟨h_in_causality, h_s1_mem, h_s2_mem⟩
    exact h_extends s1 s2 h_in_causalityMem
  · -- InstOrder: ppo ⊆ mo'
    intro i1 i2 h_ppo h_i1_mem h_i2_mem
    have h_in_causality : causalityRelPrim of aa po rf co i1 i2 := Or.inr h_ppo
    have h_in_causalityMem : causalityMem i1 i2 := ⟨h_in_causality, h_i1_mem, h_i2_mem⟩
    exact h_extends i1 i2 h_in_causalityMem
  · -- LoadValue
    intro s l a h_s_addr h_l_addr h_s_store h_l_load h_rf
    constructor
    · -- Part 1: s is visible (s po l ∨ s mo' l)
      by_cases h_same_proc : s.procId = l.procId
      · -- Same thread: s rfi l, need to show s po l
        left
        have h_neq : s ≠ l := by
          intro h_eq
          rw [h_eq] at h_s_store
          have h_load_not_store := load_not_store l h_l_load
          exact h_load_not_store h_s_store
        cases po.total s l h_same_proc h_neq with
        | inl h_s_po_l => exact h_s_po_l
        | inr h_l_po_s =>
          -- l po s with same address gives l poloc s
          -- Combined with s rf l gives SC-per-Location cycle
          exfalso
          have h_same_addr : l.sameAddrWith aa s := by
            have h_rf_same := rf.sameAddr s l h_rf
            unfold Instruction.sameAddrWith at h_rf_same ⊢
            cases h_aa_s : aa s.id with
            | none => simp [h_aa_s] at h_rf_same
            | some a_s =>
              cases h_aa_l : aa l.id with
              | none => simp [h_aa_s, h_aa_l] at h_rf_same
              | some a_l =>
                simp only [h_aa_s, h_aa_l, beq_iff_eq] at h_rf_same ⊢
                exact h_rf_same.symm
          have h_l_mem : l.isMemInst := isLoad_implies_isMemInst l h_l_load
          have h_s_mem : s.isMemInst := isStore_implies_isMemInst s h_s_store
          have h_poloc : programOrderLoc aa po l s := ⟨h_l_po_s, h_same_addr, h_l_mem, h_s_mem⟩
          -- Build SC-per-Location cycle: l poloc s rf l
          -- sc_rel' = rf ∪ co ∪ fr ∪ poloc (for primitive version)
          let sc_rel' := unionRel (unionRel (unionRel rf.rel co.rel) (fromReadsPrim aa rf co)) (programOrderLoc aa po)
          have h_rf_edge : sc_rel' s l := Or.inl (Or.inl (Or.inl h_rf))
          have h_poloc_edge : sc_rel' l s := Or.inr h_poloc
          have h_cycle : Relation.TransGen sc_rel' l l :=
            Relation.TransGen.tail (Relation.TransGen.single h_poloc_edge) h_rf_edge
          -- This contradicts SC-per-Location acyclicity
          exact h_sc l h_cycle
      · -- Different threads: s rfe l, so s mo' l by construction
        right
        have h_rfe : readFromExternal aa rf s l := ⟨h_rf, h_same_proc⟩
        have h_in_causality : causalityRelPrim of aa po rf co s l := Or.inl (Or.inl (Or.inl h_rfe))
        have h_s_mem : s.isMemInst := isStore_implies_isMemInst s h_s_store
        have h_l_mem : l.isMemInst := isLoad_implies_isMemInst l h_l_load
        have h_in_causalityMem : causalityMem s l := ⟨h_in_causality, h_s_mem, h_l_mem⟩
        exact h_extends s l h_in_causalityMem
    · -- Part 2: s is mo'-maximal among visible stores
      intro s' h_s'_store h_s'_addr h_s'_visible
      have h_s_mem : s.isMemInst := isStore_implies_isMemInst s h_s_store
      have h_s'_mem : s'.isMemInst := isStore_implies_isMemInst s' h_s'_store
      by_cases h_eq : s' = s
      · exact Or.inr h_eq
      · cases mo'.total s' s h_s'_mem h_s_mem h_eq with
        | inl h_s'_mo_s => exact Or.inl h_s'_mo_s
        | inr h_s_mo_s' =>
          -- s mo' s' leads to contradiction
          -- Key: we use the FIXED co, not derived from mo'
          exfalso
          -- s and s' are same-address stores
          have h_same_addr_s_s' : s.sameAddrWith aa s' := by
            unfold Instruction.sameAddrWith
            simp [h_s_addr, h_s'_addr]
          -- By co totality: either s co s' or s' co s
          -- Since mo' extends co and we have s mo' s', we must have s co s' or s' co s
          -- But if s' co s, then s' mo' s (since mo' extends co), contradicting s mo' s'
          have h_s_co_s' : co.rel s s' := by
            cases co.total s s' h_s_store h_s'_store h_same_addr_s_s' (Ne.symm h_eq) with
            | inl h => exact h
            | inr h_s'_co_s =>
              -- s' co s implies s' mo' s (mo' extends co)
              have h_s'_mo_s := h_extends s' s ⟨Or.inl (Or.inl (Or.inr h_s'_co_s)),
                h_s'_mem, h_s_mem⟩
              -- But we have s mo' s', and mo' is irreflexive and transitive
              have h_s_mo_s := mo'.trans s s' s h_s_mo_s' h_s'_mo_s
              exact absurd h_s_mo_s (mo'.irrefl s)
          -- Now: s rf l and s co s' gives l fr s' (using primitive fr)
          have h_l_fr_s' : fromReadsPrim aa rf co l s' :=
            ⟨h_l_load, h_s'_store, s, h_rf, h_s_co_s'⟩
          -- l fr s' is in causality, hence l mo' s'
          have h_l_mem : l.isMemInst := isLoad_implies_isMemInst l h_l_load
          have h_in_causality : causalityRelPrim of aa po rf co l s' :=
            Or.inl (Or.inr h_l_fr_s')
          have h_l_mo_s' := h_extends l s' ⟨h_in_causality, h_l_mem, h_s'_mem⟩
          -- Now check visibility of s'
          cases h_s'_visible with
          | inl h_s'_po_l =>
            -- s' po l and l mo' s' gives contradiction via po totality or cycle
            -- Actually: s' po l means same processor
            -- l mo' s' is from causality
            -- This doesn't immediately give a contradiction via mo'...
            -- But we can build an SC-per-Location cycle:
            -- s' poloc l (since same address) and l fr s' gives cycle
            have h_same_addr_s'_l : s'.sameAddrWith aa l := by
              unfold Instruction.sameAddrWith
              simp [h_s'_addr, h_l_addr]
            have h_poloc_s'_l : programOrderLoc aa po s' l :=
              ⟨h_s'_po_l, h_same_addr_s'_l, h_s'_mem, h_l_mem⟩
            -- SC cycle: s' poloc l fr s'
            let sc_rel' := unionRel (unionRel (unionRel rf.rel co.rel) (fromReadsPrim aa rf co)) (programOrderLoc aa po)
            have h_fr_edge : sc_rel' l s' := Or.inl (Or.inr h_l_fr_s')
            have h_poloc_edge : sc_rel' s' l := Or.inr h_poloc_s'_l
            have h_cycle : Relation.TransGen sc_rel' s' s' :=
              Relation.TransGen.tail (Relation.TransGen.single h_poloc_edge) h_fr_edge
            exact h_sc s' h_cycle
          | inr h_s'_mo'_l =>
            -- s' mo' l and l mo' s' gives mo' cycle - contradiction
            have h_s'_mo_s' := mo'.trans s' l s' h_s'_mo'_l h_l_mo_s'
            exact mo'.irrefl s' h_s'_mo_s'

/-- Build a CoherenceOrderPrim from the coherence order derived from mo -/
def coherenceOrderPrimFromMo (aa : AddressAssignment) (mo : MemoryOrder) : CoherenceOrderPrim aa where
  rel := coherenceOrderAll aa mo
  storesSameAddr := by
    intro s1 s2 h
    unfold coherenceOrderAll at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  irrefl := by
    intro s h
    unfold coherenceOrderAll at h
    exact mo.irrefl s h.2.2.2
  trans := by
    intro s1 s2 s3 h12 h23
    unfold coherenceOrderAll at h12 h23 ⊢
    constructor
    · exact h12.1
    constructor
    · exact h23.2.1
    constructor
    · -- s1.sameAddrWith aa s3
      have h12_same := h12.2.2.1
      have h23_same := h23.2.2.1
      unfold Instruction.sameAddrWith at h12_same h23_same ⊢
      cases h_s1 : aa s1.id with
      | none => simp [h_s1] at h12_same
      | some a1 =>
        cases h_s2 : aa s2.id with
        | none => simp [h_s1, h_s2] at h12_same
        | some a2 =>
          cases h_s3 : aa s3.id with
          | none => simp [h_s2, h_s3] at h23_same
          | some a3 =>
            simp only [h_s1, h_s2, beq_iff_eq] at h12_same
            simp only [h_s2, h_s3, beq_iff_eq] at h23_same
            simp only [beq_iff_eq]
            exact h12_same.trans h23_same
    · exact mo.trans s1 s2 s3 h12.2.2.2 h23.2.2.2
  total := by
    intro s1 s2 h1_store h2_store h_same_addr h_neq
    unfold coherenceOrderAll
    have h1_mem := isStore_implies_isMemInst s1 h1_store
    have h2_mem := isStore_implies_isMemInst s2 h2_store
    cases mo.total s1 s2 h1_mem h2_mem h_neq with
    | inl h => exact Or.inl ⟨h1_store, h2_store, h_same_addr, h⟩
    | inr h =>
      have h_same_addr_sym : s2.sameAddrWith aa s1 := by
        unfold Instruction.sameAddrWith at h_same_addr ⊢
        cases h_s1 : aa s1.id with
        | none => simp [h_s1] at h_same_addr
        | some a1 =>
          cases h_s2 : aa s2.id with
          | none => simp [h_s1, h_s2] at h_same_addr
          | some a2 =>
            simp only [h_s1, h_s2, beq_iff_eq] at h_same_addr ⊢
            exact h_same_addr.symm
      exact Or.inr ⟨h2_store, h1_store, h_same_addr_sym, h⟩

/-- fromReads (derived from mo) equals fromReadsPrim (with co from mo) -/
theorem fromReads_eq_fromReadsPrim (aa : AddressAssignment) (rf : ReadFrom aa) (mo : MemoryOrder) :
    fromReads aa rf mo = fromReadsPrim aa rf (coherenceOrderPrimFromMo aa mo) := by
  funext l s
  simp only [fromReads, fromReadsPrim, coherenceOrderPrimFromMo, coherenceOrderAll]
  apply propext
  constructor
  · intro ⟨h_load, h_store, s', h_rf, h_same, h_mo⟩
    refine ⟨h_load, h_store, s', h_rf, ?_⟩
    have h_s'_store := (rf.storeToLoad s' l h_rf).1
    exact ⟨h_s'_store, h_store, h_same, h_mo⟩
  · intro ⟨h_load, h_store, s', h_rf, h_co⟩
    refine ⟨h_load, h_store, s', h_rf, h_co.2.2.1, h_co.2.2.2⟩

/-- SC-per-Location with derived co equals SC-per-Location with primitive co -/
theorem scPerLocation_eq_scPerLocationPrim (aa : AddressAssignment) (po : ProgramOrder)
    (rf : ReadFrom aa) (mo : MemoryOrder) :
    COM_scPerLocation { po := po, mo := mo, aa := aa, rf := rf } ↔
    COM_scPerLocationPrim aa po rf (coherenceOrderPrimFromMo aa mo) := by
  unfold COM_scPerLocation COM_scPerLocationPrim
  simp only [fromReads_eq_fromReadsPrim]
  constructor <;> intro h <;> exact h

/-- Causality with derived co equals causality with primitive co -/
theorem causality_eq_causalityPrim (of : OrderedFunc) (aa : AddressAssignment) (po : ProgramOrder)
    (rf : ReadFrom aa) (mo : MemoryOrder) :
    causalityRel of { po := po, mo := mo, aa := aa, rf := rf } =
    causalityRelPrim of aa po rf (coherenceOrderPrimFromMo aa mo) := by
  unfold causalityRel causalityRelPrim
  simp only [fromReads_eq_fromReadsPrim]
  rfl

/-- COM_causality with derived co equals COM_causalityPrim -/
theorem comCausality_eq_comCausalityPrim (of : OrderedFunc) (aa : AddressAssignment)
    (po : ProgramOrder) (rf : ReadFrom aa) (mo : MemoryOrder) :
    COM_causality of { po := po, mo := mo, aa := aa, rf := rf } ↔
    COM_causalityPrim of aa po rf (coherenceOrderPrimFromMo aa mo) := by
  unfold COM_causality COM_causalityPrim
  rw [causality_eq_causalityPrim]

/-- Equivalence of GAM and COM: COM ⊆ GAM

This theorem delegates to COM_subset_GAM_prim by showing that the
coherence order derived from mo can be wrapped into a CoherenceOrderPrim.
The key insight is that COM_scPerLocation and COM_causality using
derived co are equivalent to COM_scPerLocationPrim and COM_causalityPrim
using the primitive wrapper.

Paper's proof strategy (Section 5.3):
1. Given COM axioms (SC-per-Location and Causality), construct mo as any
   total order extending the causality relation (rfe ∪ co ∪ fr ∪ ppo)
2. InstOrder holds by construction: ppo ⊆ causality ⊆ mo
3. LoadValue holds: if w rf r, then either w rfi r (so w po r by SC-per-Location)
   or w rfe r (so w mo r by construction). If w not maximal, get contradiction. -/
theorem COM_subset_GAM (of : OrderedFunc) :
    ∀ (ew : ExecutionWitness) (prog : ProgramExecution),
    ew.consistentWith prog →
    COM_scPerLocation ew →
    COM_causality of ew →
    ∃ (mo' : MemoryOrder),
      let ew' := { ew with mo := mo' }
      satisfies_InstOrder of ew' ∧
      satisfies_LoadValue ew' := by
  intro ew prog _h_cons h_sc h_caus
  -- Build the primitive co wrapper from ew.mo
  let co := coherenceOrderPrimFromMo ew.aa ew.mo
  -- Convert COM axioms to primitive form
  have h_sc_prim : COM_scPerLocationPrim ew.aa ew.po ew.rf co := by
    rw [← scPerLocation_eq_scPerLocationPrim]
    exact h_sc
  have h_caus_prim : COM_causalityPrim of ew.aa ew.po ew.rf co := by
    rw [← comCausality_eq_comCausalityPrim]
    exact h_caus
  -- Apply the primitive version
  obtain ⟨mo', _, h_instOrder, h_loadValue⟩ :=
    COM_subset_GAM_prim of ew.aa ew.po ew.rf co h_sc_prim h_caus_prim
  exact ⟨mo', h_instOrder, h_loadValue⟩

/-- Main equivalence theorem: GAM and COM are equivalent
    Assumes well-formed address assignments (only memory instructions have addresses) -/
theorem GAM_iff_COM (of : OrderedFunc) (prog : ProgramExecution) :
    (∃ ew, ew.consistentWith prog ∧
           ew.aa.onlyMemInst prog.allInstructions ∧
           satisfies_InstOrder of ew ∧
           satisfies_LoadValue ew) ↔
    (∃ ew, ew.consistentWith prog ∧
           ew.aa.onlyMemInst prog.allInstructions ∧
           COM_scPerLocation ew ∧
           COM_causality of ew) := by
  constructor
  · -- GAM → COM
    intro ⟨ew, h_cons, h_wf, h_inst, h_load⟩
    exact ⟨ew, h_cons, h_wf, GAM_subset_COM of ew prog h_cons h_wf h_inst h_load⟩
  · -- COM → GAM
    intro ⟨ew, h_cons, h_wf, h_sc, h_caus⟩
    obtain ⟨mo', h_inst', h_load'⟩ := COM_subset_GAM of ew prog h_cons h_sc h_caus
    have h_cons' : { ew with mo := mo' }.consistentWith prog := by
      unfold ExecutionWitness.consistentWith at h_cons ⊢
      exact h_cons
    exact ⟨{ ew with mo := mo' }, h_cons', h_wf, h_inst', h_load'⟩

end GamI2e
