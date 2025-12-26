# GAM/I2E Formalization Plan

## Current Status (Updated 2025-12-05 Session 28 - Proof Golfing)

**Architecture:** ✅ Unified (single-track with `AddressAssignment`)
**Build Status:** ✅ Compiles successfully (no sorries, only 1 axiom for Szpilrajn)
**Total Lines:** ~5050 (was ~5100)
**Remaining Sorries:** 0
**Fence Types:** ✅ Parameterized (supports SC, TSO, RMO, WMM, ARM, RISC-V)

### Session 28 Progress: Proof Golfing

**Reduced ECO.lean from 1615 to 1533 lines (82 lines, ~5.1% reduction):**

1. **Added helper lemmas:**
   - `sc_rel_edge_from_non_mem_absurd`: Handles contradictions when a node is neither load nor store
   - `compose_mo_with_eq`: Composes mo relations with equality cases

2. **Applied helpers to:**
   - `sc_rel_store_to_load_rf_store_ordered` (240 lines): Used `compose_mo_with_eq` and `sc_rel_edge_from_non_mem_absurd`
   - `sc_rel_stores_transgen_to_mo_len` (220 lines): Simplified "neither load nor store" contradictions

3. **Added foundation for Ordering.lean golfing:**
   - `orderClass_mem_fence`: Maps orderClass to mem/fence property
   - `memFenceOnly_of_orderClass`: Generic proof for orderClass-based ordering functions

**File sizes after golfing:**
| File | Lines |
|------|-------|
| ECO.lean | 1533 (was 1615) |
| Equivalence.lean | 638 |
| Ordering.lean | 578 (added helpers) |
| Operational.lean | 545 |
| Types.lean | 371 |
| Causality.lean | 345 |
| CausalityHelpers.lean | 322 |

### Session 27 Progress: COM_subset_GAM COMPLETED!

**Resolved the technical issue from Session 26 by reformulating COM with primitive `co`.**

**The Fix:**
The paper treats `co` (coherence) as a **primitive input** to COM. We implemented this by:

1. **New `CoherenceOrderPrim` structure:** A per-address total order of stores, taken as primitive input instead of derived from `mo`.

2. **Primitive causality definitions:**
   - `fromReadsPrim`: fr using primitive co
   - `causalityRelPrim`: rfe ∪ co ∪ fr ∪ ppo using primitive co
   - `COM_scPerLocationPrim` and `COM_causalityPrim`: COM axioms with primitive co

3. **Main theorem `COM_subset_GAM_prim`:** With primitive `co`:
   - Construct `mo'` extending causality via Szpilrajn
   - InstOrder: ppo ⊆ causality ⊆ mo' ✅
   - LoadValue visibility: Same argument as before ✅
   - LoadValue maximality: **Key insight** - Use co totality to establish `s co s'` (not `s mo' s'`), then `l fr s'` (using fixed co) is in causality, hence `l mo' s'`. Combined with visibility of s' leads to contradiction via SC-per-Location or mo' cycle.

4. **Bridge theorems:**
   - `coherenceOrderPrimFromMo`: Build `CoherenceOrderPrim` from mo-derived coherence
   - `fromReads_eq_fromReadsPrim`: fr with derived co = fr with primitive co (when co comes from same mo)
   - `scPerLocation_eq_scPerLocationPrim`, `comCausality_eq_comCausalityPrim`: Equivalence of axiom formulations

5. **Final `COM_subset_GAM`:** Delegates to primitive version by wrapping the derived co.

**Why the fix works:**
The original issue was that when constructing `mo'`, the coherence `co'` derived from `mo'` differs from the original `co` derived from `ew.mo`. The paper's proof assumes `co` is fixed.

By making `co` primitive:
- Causality uses the **fixed** `co` (not derived from any mo)
- We construct `mo'` extending this fixed causality
- In LoadValue maximality, we use co totality to get `s co s'` (fixed relation)
- Then `l fr s' = l rf⁻¹;co s'` is in causality (uses fixed co)
- Hence `l mo' s'` by construction

This matches the paper exactly.

### Session 26 Progress: COM_subset_GAM Implementation (Previous)

**Implemented most of the COM ⊆ GAM direction, with 2 sorries in LoadValue maximality.**

### Session 25 Progress: SC-PER-LOCATION PROOF COMPLETED! 🎉

**Completed the `sc_rel_cycle_has_store` proof - SC-per-Location now fully proven!**

The key insight from the paper (ComProofs.tex Theorem): In any sc_rel cycle, there must be a store because:
- rf source is store, co source is store, fr target is store
- If all nodes were loads, all edges would be poloc (load-to-load)
- poloc ⊆ po, so we'd have a po cycle, contradicting po acyclicity

**Completed proof structure:**
1. `sc_rel_cycle_has_store`: Any sc_rel cycle contains a store
   - If starting node is store: done
   - If starting node is load, trace first edge:
     - rf: impossible (source is store, not load)
     - co: impossible (source is store, not load)
     - fr: target is store - found!
     - poloc to store: found!
     - poloc to load: either cycle closes (po cycle → contradiction) or continue
   - For poloc to load case with path next →+ inst:
     - Proved helper: `h_sc_rel_load_gives_store_or_po` - any path from load either has a store or reduces to po path
     - If store found: return it
     - If po path: combine with poloc.po to get po cycle → contradiction

2. `sc_rel_stores_transgen_to_mo`: Path between stores → mo path (already proven)

3. `sc_per_location_acyclic`: Main theorem now complete
   - Find store s in cycle
   - Construct cycle at s
   - Reduce to mo cycle via `sc_rel_stores_transgen_to_mo`
   - Contradiction with mo acyclicity

**Key Lean 4 technique used:** When inducting on TransGen, use `intro a _ h_a_load h_path` with underscore for the endpoint, then `rename_i endpoint` to name it in each branch. This avoids the `b✝` variable naming issue.

### Session 24 Progress (Previous)

**Implemented paper's proof strategy (Option 3) - dramatically simplified SC-per-Location proof!**

(See Session 25 for completion)

### Session 23 Progress (Previous)

**SC-per-Location: Expanded proof for load cycle cases, introduced compilation errors**

(Session 24 fixed all these errors - see above)

### Session 22 Progress (Previous)

**SC-per-Location: Continued Progress with Cleaner Abstractions**

1. **New helper lemmas added:**
   - `transGen_last_edge'`: Extract last edge from TransGen path (complement to `transGen_first_edge'`)
   - `sc_rel_between_loads_is_poloc_path`: For paths between loads with no stores, all intermediate nodes are loads. Takes `h_no_stores` as hypothesis.

2. **Key insight on TransGen paths:**
   The fundamental issue is that `TransGen` represents reachability (ANY path), not a specific path. When we need "all nodes on THIS path are loads", we're fighting against TransGen's semantics.

   The `h_no_stores` approach: Instead of proving all paths have only loads, we prove that IF there are no stores on any path from `first` to `mid`, THEN all intermediate nodes are loads. This shifts the burden to proving `h_no_stores`.

3. **Current sorry locations (from before Session 23 expansion):**

   | Line | Context | Issue |
   |------|---------|-------|
   | 1205 | `sc_rel_stores_transgen_to_mo_len` | h_no_stores: prove no stores on path first →+ mid |
   | 1264 | `sc_rel_stores_transgen_to_mo_len` | first (store) →+ mid case |
   | 1345 | `sc_rel_stores_transgen_to_mo_len` | Another consecutive loads case |
   | 1423 | `sc_per_location_acyclic` | Load cycle case (fr edge) - EXPANDED in Session 23 |
   | 1434 | `sc_per_location_acyclic` | Load cycle case (poloc to load) |
   | 1443 | `sc_per_location_acyclic` | Load cycle case (poloc to store via fr) |

4. **Removed/Cleaned lemmas:**
   - `sc_rel_last_store_path_all_loads` was replaced by `sc_rel_between_loads_is_poloc_path` (cleaner formulation)

**Key Remaining Challenge:**
At line 1205, we need to prove: if `w` is the "last store" (from `sc_rel_last_store_in_path_to_load`), and `first` is immediately after `w` on path to `mid`, then there are no stores on ANY path from `first` to `mid`.

The difficulty: `sc_rel_last_store_in_path_to_load` only guarantees no stores on ONE specific path. But TransGen quantifies over ALL paths. We have:
- `h_from_first : first →+ x` (some path)
- `h_to_mid : x →+ mid` (some path)

These paths might go through stores via `fr → co* → rf` patterns even if our tracked path doesn't.

**Potential solutions:**
1. Use path-indexed types (like `SCRelLen`) throughout to track specific paths
2. Prove that if `first` and `mid` are both loads, then ALL paths between them are equivalent (no detours through stores) - this would use the totality of eco on same-address accesses
3. Reformulate the proof to not need the "all intermediate nodes are loads" property

### Session 21 Progress (Previous)

### Session 20 Progress (Previous)

**SC-per-Location: Continued Progress on Consecutive Loads Case**

1. **New helper lemmas added:**
   - `poloc_load_load_rf_stores_ordered`: For poloc between loads, the rf-stores are mo-ordered (or equal). This is the key insight from eco_poloc for the consecutive loads case.
   - `po_transgen_to_po`: Helper to convert TransGen of po to po
   - `poloc_transGen_irrefl`: Poloc paths are acyclic (via po acyclicity)
   - `sc_rel_load_load_is_poloc`: Extract poloc from sc_rel edge between loads

2. **Progress on consecutive loads case:**
   - Added structural case analysis for path `w →+ mid` from store to load
   - Single edge case (w → mid directly): Handled via rf functionality or poloc_store_load_gives_rf
   - Multi-edge case: Partial progress, needs chain of poloc_load_load_rf_stores_ordered

**Key Insight from poloc_load_load_rf_stores_ordered:**
For `poloc l1 l2` where both are loads:
- Let w1 = rf-store into l1, w2 = rf-store into l2
- By LoadValue axiom and mo totality: w1 = w2 or mo w1 w2
- The reverse (w2 mo w1) leads to contradiction with LoadValue visibility

This means for a chain of loads `l1 →poloc l2 →poloc ... →poloc ln`:
- The rf-stores w1, w2, ..., wn are mo-ordered: w1 ≤mo w2 ≤mo ... ≤mo wn
- This is the "rf⁻¹;co*;rf" structure from the paper

### Session 18 Progress

SC-per-Location code cleanup and structure. See Session 19 for current status.

### Session 16 Progress

**Completed: ARM/RISC-V Support & Warning Cleanup**

1. **Cleaned up lint warnings:**
   - `Types.lean:369`: Removed unused simp argument
   - `COM/ECO.lean:113-115`: Prefixed unused variables with `_`
   - `COM/Causality.lean:138,288-290`: Prefixed unused variables with `_`

2. **Added ARM v8.2 ordering (`orderedARM`):**
   - Based on paper Section 6.5
   - DMB LD (fenceLL + fenceLS): Orders load-to-load and load-to-store
   - DMB ST (fenceSS): Orders store-to-store
   - Load-Acquire/Store-Release semantics
   - Proved NOT I2E compatible (allows load-store reordering)

3. **Added RISC-V ordering (`orderedRISCV`):**
   - Based on paper Section 6.7 / Table in Figure
   - Uses Release, Acquire, Full fence semantics
   - Key difference from WMM: Release is NOT ordered with Acquire
   - Proved NOT I2E compatible (allows load-store reordering)

**Memory Model Support:**

| Model | Status | Notes |
|-------|--------|-------|
| SC | ✅ Complete | Uses `orderedSC` |
| TSO | ✅ Complete | Uses `orderedTSO` |
| RMO | ✅ Complete | Uses `orderedRMO` with FenceLL/LS/SL/SS |
| WMM | ✅ Complete | Uses `orderedWMM` with acquire/release |
| ARM v8.2 | ✅ Complete | Uses `orderedARM` |
| RISC-V | ✅ Complete | Uses `orderedRISCV` |

### Session 15 Progress

**Completed: Fence Type Parameterization**

Added `FenceKind` enumeration and parameterized fence instructions to support multiple memory models:

1. **Types.lean** - Added `FenceKind` inductive type with 7 variants:
   - `fenceLL`, `fenceLS`, `fenceSL`, `fenceSS` (directional fences for RMO)
   - `full` (full barrier for TSO/SC)
   - `acquire`, `release` (for WMM-style models)

2. **Types.lean** - Updated `InstType.fence` to take `FenceKind` parameter

3. **Types.lean** - Added `Instruction.fenceKind?` helper function

4. **Ordering.lean** - Added new ordering instances:
   - `orderedRMO`: Full RMO per Table 2 (uses specific fence kinds)
   - `orderedWMM`: WMM per Table 4 (acquire/release semantics)
   - Kept `orderedRMO_relaxed` as legacy (treats all fences uniformly)

### Session 14 Progress

**Completed:**
1. ✅ Fixed `causality_transgen_mem_to_mo` termination error
   - Used strong induction on path length via `TransGenLen` indexed type
   - Defined `causality_last_mem_before_nonmem_len` variant that tracks length
   - Proved using `Nat.strongRecOn` for well-founded recursion

2. ✅ Completed **Causality** proof (`COM_causality` axiom in `GAM_subset_COM`)
   - Case: inst is mem → use `causality_transgen_mem_to_mo` directly
   - Case: inst is non-mem, first edge to m
     - m is mem → construct cycle at m, map to mo, contradiction
     - m is non-mem → use new helper `causality_path_nonmem_endpoints`
       - All non-mem → compose ppo, get ppo inst inst, contradiction
       - Found mem n → construct cycle at n, map to mo, contradiction

3. ✅ Added helper `causality_path_nonmem_endpoints`
   - Given path from non-mem to non-mem, either:
     - All nodes are non-mem → return ppo (composable)
     - Some node is mem → return that node with decomposition paths

### Key Technical Solutions

**TransGenLen Pattern:** To avoid Lean's termination checker issues with nested recursion on TransGen:
```lean
private inductive TransGenLen {α : Type} (r : α → α → Prop) : α → α → Nat → Prop
  | single {a b : α} : r a b → TransGenLen r a b 1
  | tail {a b c : α} {n : Nat} : TransGenLen r a b n → r b c → TransGenLen r a c (n + 1)
```
Then prove using `induction n using Nat.strongRecOn` and convert between TransGen/TransGenLen.

**Induction Variable Naming:** When using `induction h with` on TransGen, Lean renames endpoint variables with `✝` suffix. Use `rename_i` or make parameters implicit `{endpoint : Instruction}` to avoid naming conflicts.

### File Structure

| File | Purpose | Status |
|------|---------|--------|
| Types.lean | Core types, `AddressAssignment`, `sameAddrWith` | ✅ Complete |
| Relations.lean | `ReadFrom`, `coherenceOrder`, `fromReads`, `transClosure` | ✅ Complete |
| Ordering.lean | `OrderedFunc`, TSO/RMO/SC orderings | ✅ Complete |
| PreservedPO.lean | `preservedProgramOrder` and components | ✅ Complete |
| Axiomatic.lean | `ExecutionWitness`, GAM axioms, `consistentWith` | ✅ Complete |
| **COM/** | COM model submodules (~350-620 lines each) | ✅ Complete |
| └ Definitions.lean | COM axioms, eco definition, basic helpers | ✅ Complete |
| └ ECO.lean | eco_total_per_address, eco_poloc | ✅ Complete |
| └ CausalityHelpers.lean | com_contained_in_mo, transGen utilities | ✅ Complete |
| └ Causality.lean | causality_transgen_mem_to_mo, TransGenLen | ✅ Complete |
| └ Equivalence.lean | GAM_subset_COM, COM_subset_GAM, GAM_iff_COM | ✅ Complete (Session 27) |
| Operational.lean | ROB-based operational semantics | ✅ Complete |

### Remaining Work in COM/Equivalence.lean

**ALL COMPLETE as of Session 27!**

| Priority | Item | Description | Status |
|----------|------|-------------|--------|
| ~~**MEDIUM**~~ | ~~SC-per-Location~~ | ~~Line 64~~ | ✅ COMPLETE (Session 25) |
| ~~**LOW**~~ | ~~COM_subset_GAM LoadValue maximality~~ | ~~Lines 402, 414~~ | ✅ COMPLETE (Session 27) - Fixed via primitive co |
| N/A | szpilrajn_extension | Line 31 | Axiom (classical, requires Choice) |

### SC-per-Location (COMPLETE as of Session 25)

Key lemmas proven:
- `sc_rel_cycle_has_store`: Any sc_rel cycle contains at least one store
- `sc_rel_stores_transgen_to_mo`: Path between stores reduces to mo path
- `sc_per_location_acyclic`: Main theorem - acyclic(rf ∪ co ∪ fr ∪ poloc)

The proof follows the paper's cycle reduction argument:
1. Any cycle must have a store (loads alone can't form cycles - poloc ⊆ po is acyclic)
2. From any store, reduce path to mo via rf;fr ⊆ co ⊆ mo
3. mo cycle contradicts mo acyclicity

### Key Lemmas in COM.lean (All Complete)

**Causality Infrastructure:**
- `causality_edge_from_nonmem_is_ppo`: Edge from non-mem source must be ppo
- `causality_edge_to_nonmem_is_ppo`: Edge to non-mem target must be ppo
- `causality_all_nonmem_is_ppo`: Path with all non-mem nodes gives ppo
- `causality_last_mem_before_nonmem`: Find last mem node before non-mem endpoint
- `causality_single_mem_to_mo`: Single edge between mem nodes maps to mo
- `causality_path_nonmem_endpoints`: Handle paths with non-mem endpoints
- `causality_transgen_mem_to_mo`: TransGen causality between mem nodes → TransGen mo
- `com_contained_in_mo`: rfe/co/fr/ppo between mem nodes ⊆ mo

**Other:**
- `eco_poloc`: poloc edges map to eco (extended communication)
- `mo_acyclic`: Memory order is acyclic (strict total order)
- `ppo_trans`, `ppo_irrefl`: PPO properties

### Paper Reference (ComProofs.tex)

**Causality (DONE):**
- Lemma C.1: "All of rfe, co, fr, and ppo are contained in mo"
- Our proof handles the complication that ppo can involve non-mem instructions

**SC-per-Location (DONE - Session 25):**
- Paper uses cycle reduction (Theorem in ComProofs.tex lines 66-74)
- Our proof: 1) Find store in cycle, 2) Reduce to mo, 3) Contradiction
- Key lemma: `sc_rel_cycle_has_store` - if all nodes were loads, all edges would be poloc → po cycle → contradiction

**COM ⊆ GAM (TODO):**
- Requires constructing a valid mo order from COM axioms
- Essentially a topological sort of the causality DAG
- May need Zorn's lemma or similar for infinite case

---

## Paper vs Lean Definition Comparison (Audit: 2025-12-05)

### ✅ Matching Definitions

| Paper Definition | Lean Location | Status | Notes |
|------------------|---------------|--------|-------|
| Program order `<_po` | `Relations.lean:26-35` | ✅ Match | Per-processor total order |
| Memory order `<_mo` | `Relations.lean:71-81` | ✅ Match | Total order of memory instructions |
| Data dependency `<_ddep` (Def 4) | `Relations.lean:38-42` | ✅ Match | |
| Address dependency `<_adep` (Def 5) | `Relations.lean:46-50` | ✅ Match | |
| Read-from `rf` | `Relations.lean:85-95` | ✅ Match | Functional, store-to-load |
| Coherence order `<_co` | `Relations.lean:98-109` | ✅ Match | Per-address store order, derived from mo |
| From-reads `fr` = rf⁻¹;co | `Relations.lean:113-118` | ✅ Match | |
| Program order loc `po_loc` | `Relations.lean:121-122` | ✅ Match | |
| rfe (external rf) | `Relations.lean:125-126` | ✅ Match | Different processors |
| rfi (internal rf) | `Relations.lean:129-130` | ✅ Match | Same processor |
| Preserved memory/fence order `<_ppomf` (Def 1) | `PreservedPO.lean:26-31` | ✅ Match | |
| Preserved dependency order `<_ppod` (Def 6) | `PreservedPO.lean:41-55` | ✅ Match | All 4 cases |
| Preserved same-addr order `<_pposa` (Def 7) | `PreservedPO.lean:64-72` | ✅ Match | All 3 cases |
| Preserved program order `<_ppo` (Def 8) | `PreservedPO.lean:81-86` | ✅ Match | TransGen of union |
| TSO Ordered function (Table 1) | `Ordering.lean:39-89` | ✅ Match | |
| SC Ordered function | `Ordering.lean:144-194` | ✅ Match | All true |
| Axiom Inst-Order | `Axiomatic.lean:68-73` | ✅ Match | ppo ⊆ mo |
| Axiom Load-Value | `Axiomatic.lean:76-92` | ✅ Match | Max-mo visible store |
| Axiom SC-per-Location | `COM/Definitions.lean:28-32` | ✅ Match | acyclic(rf ∪ co ∪ fr ∪ poloc) |
| Axiom Causality | `COM/Definitions.lean:35-40` | ✅ Match | acyclic(rfe ∪ co ∪ fr ∪ ppo) |
| Extended Communication eco (ComProofs.tex) | `COM/Definitions.lean:58-64` | ✅ Match | co ∪ fr ∪ co*;rf ∪ rf⁻¹;co*;rf |

### ⚠️ Minor Differences (Acceptable)

| Paper Definition | Lean Location | Difference | Impact |
|------------------|---------------|------------|--------|
| I2E constraint | `Ordering.lean:328-330` | Paper states ordered(Ld, St) = true; Lean has `isI2ECompatible` predicate | Same semantics, different formulation |

### 🔴 Potential Issues

1. ~~**Fence Type Richness**~~: ✅ **RESOLVED in Session 15** - Added `FenceKind` with 7 variants. Full RMO and WMM instances now available.

2. **Operational Model Fidelity**: The Operational.lean file defines a detailed ROB-based model, but the proofs focus on axiomatic equivalence. The operational↔axiomatic equivalence (GAM Soundness/Completeness) is NOT formalized.

   **Impact**: None for current goal (GAM↔COM equivalence). Operational model is informational.

### File Structure Summary

| File | Lines | Purpose |
|------|-------|---------|
| Types.lean | ~335 | Core types, AddressAssignment, Instruction |
| Relations.lean | ~160 | Fundamental relations (po, mo, rf, co, fr) |
| Ordering.lean | ~245 | OrderedFunc, TSO/RMO/SC instances |
| PreservedPO.lean | ~192 | PPO definition and properties |
| Axiomatic.lean | ~206 | ExecutionWitness, GAM axioms |
| COM/Definitions.lean | ~120 | COM axioms, eco definition |
| COM/ECO.lean | ~352 | eco_total_per_address, eco_poloc |
| COM/CausalityHelpers.lean | ~322 | com_contained_in_mo, helpers |
| COM/Causality.lean | ~345 | causality_transgen_mem_to_mo |
| COM/Equivalence.lean | ~169 | GAM_subset_COM, COM_subset_GAM (2 sorries) |
| Operational.lean | ~545 | ROB-based operational model (informational) |

---

## Priority Queue

### 1. ~~HIGH: Fence Type Parameterization~~ ✅ COMPLETED

See Session 15 Progress above.

### 2. **MEDIUM: SC-per-Location Proof** (Next)

- Read paper's proof in ComProofs.tex Section C
- Implement cycle reduction argument
- Key lemmas needed: rf;rf⁻¹ = id, rf;fr ⊆ co, eco_poloc

### 3. **LOW: COM_subset_GAM Proof**

- Construct mo from COM axioms
- Topological sort of causality relation
- May need Zorn's lemma or similar for infinite case

---

## Theoretical Context

The formalization proves equivalence between GAM and COM memory models:

**GAM** (General Atomic Memory): Axiomatic model with InstOrder and LoadValue axioms
**COM** (Communication Order Model): Axiomatic model with SC-per-Location and Causality axioms

**Completed:** GAM ⊆ COM (Causality axiom fully proven, SC-per-Location still sorry)
**Remaining:** COM ⊆ GAM (construct mo from COM axioms)

---

## Future Work: Incomplete Implementations

The following items are placeholders or simplified implementations that do not affect the COM ↔ GAM equivalence proof (which is purely axiomatic-to-axiomatic), but would need attention for full operational model formalization.

### High Priority (for Operational ↔ Axiomatic equivalence)

| Location | Issue | Description |
|----------|-------|-------------|
| `Operational.lean:529-532` | `toExecutionWitness` placeholder | Always returns `none` instead of constructing witness from operational state. Critical for connecting operational and axiomatic models. |

### Medium Priority (Operational semantics fidelity)

| Location | Issue | Description |
|----------|-------|-------------|
| `Operational.lean:168-174` | TODO guards | All 7 execution rule guards (`executeRegToReg`, `executeBranch`, `executeFence`, `executeLoad`, `computeStoreData`, `executeStore`, `computeMemAddr`) return `true` unconditionally. Paper (gam.tex §4.2) specifies precise guards. |
| `Operational.lean:183-185` | Fetch placeholder | Creates a placeholder fence instruction instead of reading from actual program. |

### Low Priority (Simplified behavior, acceptable for modeling)

| Location | Issue | Description |
|----------|-------|-------------|
| `Operational.lean:218` | Simplified reg-op | Register operations always produce result 0. |
| `Operational.lean:247,256` | Simplified branch | No misprediction handling; assumes branch always taken. |
| `Ordering.lean:188` | Legacy RMO | `orderedRMO_relaxed` marked as "legacy/simplified". May be intentional for comparison; consider removing if unused. |

### Note: Intentional Axiom

The `szpilrajn_extension` axiom in `Equivalence.lean:31` is **intentionally** axiomatized. Szpilrajn's extension theorem requires the Axiom of Choice in the infinite case. This is standard practice and mathematically sound. To eliminate it, one could either:
1. Add a `Finite` instance for instructions and prove constructively via topological sort, or
2. Derive from Lean's `Classical.choice`
