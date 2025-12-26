/-
Ordering function and parameterization for GAM/I2E.

This module defines the Ordered function that parameterizes
the memory model by instruction and fence orderings.
-/

import GamI2e.Types
import GamI2e.Relations

namespace GamI2e

/-- The Ordered function: determines if instruction i_old should be
    ordered before i_new according to the memory/fence ordering.
    This is the key parameter of the GAM framework. -/
structure OrderedFunc where
  /-- The ordering function -/
  ordered : Instruction → Instruction → Bool
  /-- If ordered returns true, both instructions must be memory/fence instructions -/
  memFenceOnly : ∀ i1 i2, ordered i1 i2 = true →
    (i1.isMemInst ∨ i1.isFence) ∧ (i2.isMemInst ∨ i2.isFence)

/-- Helper to classify instruction for ordering purposes -/
inductive OrderClass where
  | ld : OrderClass      -- Load
  | st : OrderClass      -- Store
  | fence : OrderClass   -- Fence (can be further subdivided)
  | other : OrderClass   -- Non-memory/fence instruction

/-- Get the ordering class of an instruction -/
def Instruction.orderClass (i : Instruction) : OrderClass :=
  match i.instType with
  | .load _ _ => .ld
  | .store _ _ => .st
  | .fence _ => .fence
  | _ => .other

/-- Helper: orderClass matches mem/fence for ld/st/fence -/
private theorem orderClass_mem_fence (i : Instruction) :
    i.orderClass = .ld ∨ i.orderClass = .st ∨ i.orderClass = .fence →
    i.isMemInst ∨ i.isFence := by
  intro h
  match h_t : i.instType with
  | .load _ _ =>
    left; simp [Instruction.isMemInst, h_t]
  | .store _ _ =>
    left; simp [Instruction.isMemInst, h_t]
  | .fence _ =>
    right; simp [Instruction.isFence, h_t]
  | .regOp _ _ _ =>
    simp [Instruction.orderClass, h_t] at h
  | .branch _ _ =>
    simp [Instruction.orderClass, h_t] at h

/-- Generic memFenceOnly proof for orderClass-based ordered functions -/
private theorem memFenceOnly_of_orderClass
    (f : Instruction → Instruction → Bool)
    (h_def : ∀ i1 i2, f i1 i2 = true →
      (i1.orderClass = .ld ∨ i1.orderClass = .st ∨ i1.orderClass = .fence) ∧
      (i2.orderClass = .ld ∨ i2.orderClass = .st ∨ i2.orderClass = .fence)) :
    ∀ i1 i2, f i1 i2 = true → (i1.isMemInst ∨ i1.isFence) ∧ (i2.isMemInst ∨ i2.isFence) := by
  intro i1 i2 h_ord
  have ⟨h1, h2⟩ := h_def i1 i2 h_ord
  exact ⟨orderClass_mem_fence i1 h1, orderClass_mem_fence i2 h2⟩

/-- TSO ordering function (Table 1 in paper) -/
def orderedTSO : OrderedFunc where
  ordered := fun i1 i2 =>
    match i1.orderClass, i2.orderClass with
    | .ld, .ld => true
    | .ld, .st => true
    | .ld, .fence => true
    | .st, .ld => false  -- Only relaxed ordering in TSO
    | .st, .st => true
    | .st, .fence => true
    | .fence, .ld => true
    | .fence, .st => true
    | .fence, .fence => true
    | _, _ => false
  memFenceOnly := by
    intro i1 i2 h_ord
    -- Case analysis on instruction types
    match h_t1 : i1.instType, h_t2 : i2.instType with
    | .load _ _, .load _ _ =>
      constructor <;> (left; simp [Instruction.isMemInst, h_t1, h_t2])
    | .load _ _, .store _ _ =>
      constructor <;> (left; simp [Instruction.isMemInst, h_t1, h_t2])
    | .load _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .load _ _, .regOp _ _ _ | .load _ _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .store _ _, .load _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .store _ _, .store _ _ =>
      constructor <;> (left; simp [Instruction.isMemInst, h_t1, h_t2])
    | .store _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .store _ _, .regOp _ _ _ | .store _ _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .fence _, .load _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .store _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .fence _ =>
      constructor <;> (right; simp [Instruction.isFence, h_t1, h_t2])
    | .fence _, .regOp _ _ _ | .fence _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .regOp _ _ _, _ | .branch _ _, _ =>
      simp [Instruction.orderClass, h_t1] at h_ord

/-- RMO ordering with four separate fences (Table 2 in paper)

    From the paper Table 2, RMO has these fence types with their ordering behavior:
    - FenceLL: Orders (Ld, FenceLL) and (FenceLL, Ld)
    - FenceLS: Orders (Ld, FenceLS) and (FenceLS, St)
    - FenceSL: Orders (St, FenceSL) and (FenceSL, Ld)
    - FenceSS: Orders (St, FenceSS) and (FenceSS, St)

    Memory operations are NOT ordered with each other (all relaxed).
    Fence-fence pairs are NOT ordered. -/
def orderedRMO : OrderedFunc where
  ordered := fun i1 i2 =>
    match i1.instType, i2.instType with
    -- Load before fence
    | .load _ _, .fence .fenceLL => true   -- Ld → FenceLL
    | .load _ _, .fence .fenceLS => true   -- Ld → FenceLS
    | .load _ _, .fence .full => true      -- Ld → FullFence (orders everything)
    | .load _ _, .fence .acquire => true   -- Ld → Acquire
    -- Store before fence
    | .store _ _, .fence .fenceSL => true  -- St → FenceSL
    | .store _ _, .fence .fenceSS => true  -- St → FenceSS
    | .store _ _, .fence .full => true     -- St → FullFence
    | .store _ _, .fence .release => true  -- St → Release
    -- Fence before load
    | .fence .fenceLL, .load _ _ => true   -- FenceLL → Ld
    | .fence .fenceSL, .load _ _ => true   -- FenceSL → Ld
    | .fence .full, .load _ _ => true      -- FullFence → Ld
    | .fence .acquire, .load _ _ => true   -- Acquire → Ld
    -- Fence before store
    | .fence .fenceLS, .store _ _ => true  -- FenceLS → St
    | .fence .fenceSS, .store _ _ => true  -- FenceSS → St
    | .fence .full, .store _ _ => true     -- FullFence → St
    | .fence .release, .store _ _ => true  -- Release → St
    -- Everything else is relaxed
    | _, _ => false
  memFenceOnly := by
    intro i1 i2 h_ord
    match h_t1 : i1.instType, h_t2 : i2.instType with
    | .load _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .store _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .fence _, .load _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .store _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .load _ _, .load _ _ | .load _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .load _ _, .regOp _ _ _ | .load _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .load _ _ | .store _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .regOp _ _ _ | .store _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .fence _, .fence _ =>
      simp [h_t1, h_t2] at h_ord
    | .fence _, .regOp _ _ _ | .fence _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .regOp _ _ _, _ | .branch _ _, _ =>
      simp [h_t1] at h_ord

/-- Legacy: RMO with all fences treated uniformly (simplified version) -/
def orderedRMO_relaxed : OrderedFunc where
  ordered := fun i1 i2 =>
    match i1.orderClass, i2.orderClass with
    | .ld, .ld => false      -- Relaxed
    | .ld, .st => false      -- Relaxed
    | .ld, .fence => true    -- Fences order with loads
    | .st, .ld => false      -- Relaxed
    | .st, .st => false      -- Relaxed
    | .st, .fence => true    -- Fences order with stores
    | .fence, .ld => true    -- Fences order with loads
    | .fence, .st => true    -- Fences order with stores
    | .fence, .fence => false -- Fences unordered with each other
    | _, _ => false
  memFenceOnly := by
    intro i1 i2 h_ord
    match h_t1 : i1.instType, h_t2 : i2.instType with
    | .load _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .store _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .fence _, .load _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .store _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .load _ _, .load _ _ | .load _ _, .store _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .load _ _, .regOp _ _ _ | .load _ _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .store _ _, .load _ _ | .store _ _, .store _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .store _ _, .regOp _ _ _ | .store _ _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .fence _, .fence _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .fence _, .regOp _ _ _ | .fence _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .regOp _ _ _, _ | .branch _ _, _ =>
      simp [Instruction.orderClass, h_t1] at h_ord

/-- Sequential Consistency: all orderings enforced -/
def orderedSC : OrderedFunc where
  ordered := fun i1 i2 =>
    match i1.orderClass, i2.orderClass with
    | .ld, .ld => true
    | .ld, .st => true
    | .ld, .fence => true
    | .st, .ld => true
    | .st, .st => true
    | .st, .fence => true
    | .fence, .ld => true
    | .fence, .st => true
    | .fence, .fence => true
    | _, _ => false
  memFenceOnly := by
    intro i1 i2 h_ord
    -- Same as TSO proof structure
    match h_t1 : i1.instType, h_t2 : i2.instType with
    | .load _ _, .load _ _ =>
      constructor <;> (left; simp [Instruction.isMemInst, h_t1, h_t2])
    | .load _ _, .store _ _ =>
      constructor <;> (left; simp [Instruction.isMemInst, h_t1, h_t2])
    | .load _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .load _ _, .regOp _ _ _ | .load _ _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .store _ _, .load _ _ =>
      constructor <;> (left; simp [Instruction.isMemInst, h_t1, h_t2])
    | .store _ _, .store _ _ =>
      constructor <;> (left; simp [Instruction.isMemInst, h_t1, h_t2])
    | .store _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .store _ _, .regOp _ _ _ | .store _ _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .fence _, .load _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .store _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .fence _ =>
      constructor <;> (right; simp [Instruction.isFence, h_t1, h_t2])
    | .fence _, .regOp _ _ _ | .fence _, .branch _ _ =>
      simp [Instruction.orderClass, h_t1, h_t2] at h_ord
    | .regOp _ _ _, _ | .branch _ _, _ =>
      simp [Instruction.orderClass, h_t1] at h_ord

/-- WMM ordering (Table 4 in paper)

    WMM uses two fence types:
    - Commit (Release): Orders prior stores before subsequent operations
    - Reconcile (Acquire): Orders prior loads before subsequent operations

    From Table 4:
    - Same-address operations are always ordered (Ld-Ld, Ld-St, St-St)
    - Commit orders (St, Commit) and (Commit, Ld/St)
    - Reconcile orders (Ld, Reconcile) and (Reconcile, Ld/St)

    Note: WMM models same-address ordering separately via pposa, not via ordered().
    Here we model just the fence effects. -/
def orderedWMM : OrderedFunc where
  ordered := fun i1 i2 =>
    match i1.instType, i2.instType with
    -- Stores before Release/Commit fence
    | .store _ _, .fence .release => true
    | .store _ _, .fence .full => true
    -- Loads before Acquire/Reconcile fence
    | .load _ _, .fence .acquire => true
    | .load _ _, .fence .full => true
    -- Release/Commit fence before any memory op
    | .fence .release, .load _ _ => true
    | .fence .release, .store _ _ => true
    | .fence .full, .load _ _ => true
    | .fence .full, .store _ _ => true
    -- Acquire/Reconcile fence before any memory op
    | .fence .acquire, .load _ _ => true
    | .fence .acquire, .store _ _ => true
    -- Full fence is both acquire and release
    -- (already covered above)
    | _, _ => false
  memFenceOnly := by
    intro i1 i2 h_ord
    match h_t1 : i1.instType, h_t2 : i2.instType with
    | .load _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .store _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .fence _, .load _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .store _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .load _ _, .load _ _ | .load _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .load _ _, .regOp _ _ _ | .load _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .load _ _ | .store _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .regOp _ _ _ | .store _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .fence _, .fence _ =>
      simp [h_t1, h_t2] at h_ord
    | .fence _, .regOp _ _ _ | .fence _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .regOp _ _ _, _ | .branch _ _, _ =>
      simp [h_t1] at h_ord

/-- I2E requirement: Load-Store ordering must be enforced -/
def OrderedFunc.isI2ECompatible (of : OrderedFunc) : Prop :=
  ∀ i1 i2, i1.isLoad → i2.isStore → of.ordered i1 i2 = true

/-- TSO is I2E compatible -/
theorem orderedTSO_isI2ECompatible : orderedTSO.isI2ECompatible := by
  intro i1 i2 h_load h_store
  -- Unfold isI2ECompatible and simplify
  simp [Instruction.isLoad, Instruction.isStore] at *
  -- Case analysis on instruction types
  cases h_t1 : i1.instType with
  | load _ _ =>
    cases h_t2 : i2.instType with
    | store _ _ =>
      -- load-store case: TSO orders them (ld, st) => true
      simp [orderedTSO, Instruction.orderClass, h_t1, h_t2]
    | _ => simp [h_t2] at h_store
  | _ => simp [h_t1] at h_load

/-- SC is I2E compatible -/
theorem orderedSC_isI2ECompatible : orderedSC.isI2ECompatible := by
  intro i1 i2 h_load h_store
  simp [Instruction.isLoad, Instruction.isStore] at *
  cases h_t1 : i1.instType with
  | load _ _ =>
    cases h_t2 : i2.instType with
    | store _ _ =>
      -- load-store case: SC orders them (ld, st) => true
      simp [orderedSC, Instruction.orderClass, h_t1, h_t2]
    | _ => simp [h_t2] at h_store
  | _ => simp [h_t1] at h_load

/-- RMO relaxed is NOT I2E compatible (allows Load-Store reordering) -/
theorem orderedRMO_not_isI2ECompatible : ¬orderedRMO_relaxed.isI2ECompatible := by
  intro h_compat
  -- Show a counterexample: there exist load and store where ordered returns false
  simp [OrderedFunc.isI2ECompatible] at h_compat
  -- Create a load and a store instruction with explicit type annotations
  let i_load : Instruction := ⟨(0 : Nat), (0 : Nat), .load (.literal (0 : Nat)) (0 : Nat)⟩
  let i_store : Instruction := ⟨(1 : Nat), (0 : Nat), .store (.literal (1 : Nat)) (.literal (0 : Nat))⟩
  -- Apply the compatibility hypothesis
  have h := h_compat i_load i_store
  simp [Instruction.isLoad, Instruction.isStore] at h
  -- But RMO returns false for load-store
  have h_false : orderedRMO_relaxed.ordered i_load i_store = false := by
    simp [orderedRMO_relaxed, Instruction.orderClass, i_load, i_store]
  -- Contradiction
  simp [h_false] at h

/-- ARM v8.2 ordering (Section 6.5 in paper)

    ARM v8.2 uses:
    - DMB LD (fenceLL + fenceLS): Orders load-to-load and load-to-store
    - DMB ST (fenceSS): Orders store-to-store
    - Load-Acquire (acquire): Orders subsequent loads/stores after this load
    - Store-Release (release): Orders prior loads/stores before this store

    Note: ARM allows RSW behavior which GAM forbids. This models the
    GAM-compatible subset (same-address loads are ordered via pposa).

    Memory operations are NOT ordered with each other (relaxed).
    This is similar to RMO but with ARM-specific fence semantics. -/
def orderedARM : OrderedFunc where
  ordered := fun i1 i2 =>
    match i1.instType, i2.instType with
    -- Load before fence (DMB LD / full / acquire)
    | .load _ _, .fence .fenceLL => true   -- Ld → DMB LD (LL component)
    | .load _ _, .fence .fenceLS => true   -- Ld → DMB LD (LS component)
    | .load _ _, .fence .full => true      -- Ld → Full DMB
    | .load _ _, .fence .acquire => true   -- Ld → Acquire fence
    -- Store before fence (DMB ST / full / release)
    | .store _ _, .fence .fenceSS => true  -- St → DMB ST
    | .store _ _, .fence .full => true     -- St → Full DMB
    | .store _ _, .fence .release => true  -- St → Release fence
    -- Fence before load (DMB LD / full / acquire)
    | .fence .fenceLL, .load _ _ => true   -- DMB LD → Ld
    | .fence .fenceLS, .load _ _ => true   -- DMB LD → Ld (LS orders ld-st, also ld-ld)
    | .fence .full, .load _ _ => true      -- Full DMB → Ld
    | .fence .acquire, .load _ _ => true   -- Acquire → Ld
    -- Fence before store (DMB LD(LS) / DMB ST / full / release)
    | .fence .fenceLS, .store _ _ => true  -- DMB LD → St (the LS part)
    | .fence .fenceSS, .store _ _ => true  -- DMB ST → St
    | .fence .full, .store _ _ => true     -- Full DMB → St
    | .fence .release, .store _ _ => true  -- Release → St
    -- Everything else is relaxed
    | _, _ => false
  memFenceOnly := by
    intro i1 i2 h_ord
    match h_t1 : i1.instType, h_t2 : i2.instType with
    | .load _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .store _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .fence _, .load _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .store _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .load _ _, .load _ _ | .load _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .load _ _, .regOp _ _ _ | .load _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .load _ _ | .store _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .regOp _ _ _ | .store _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .fence _, .fence _ =>
      simp [h_t1, h_t2] at h_ord
    | .fence _, .regOp _ _ _ | .fence _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .regOp _ _ _, _ | .branch _ _, _ =>
      simp [h_t1] at h_ord

/-- RISC-V ordering (Table from Section 6.7 in paper)

    From the paper's Table for RISC-V:
    - Memory operations are NOT ordered with each other (Ld-Ld, Ld-St, St-Ld, St-St all False)
    - Fences: Release, Acquire, Full
    - Ld → Release, Acquire, Full: True
    - St → Release, Full: True; St → Acquire: False
    - Release → St, Release, Full: True; Release → Ld, Acquire: False
    - Acquire → Ld, St, Release, Acquire, Full: all True
    - Full → everything: True

    Key difference from WMM: Release is NOT ordered with Acquire
    (in WMM, Commit is ordered with Reconcile) -/
def orderedRISCV : OrderedFunc where
  ordered := fun i1 i2 =>
    match i1.instType, i2.instType with
    -- Load before fence
    | .load _ _, .fence .release => true   -- Ld → Release
    | .load _ _, .fence .acquire => true   -- Ld → Acquire
    | .load _ _, .fence .full => true      -- Ld → Full
    -- Store before fence
    | .store _ _, .fence .release => true  -- St → Release
    | .store _ _, .fence .full => true     -- St → Full
    -- Store → Acquire is False (notable!)
    -- Release fence orderings
    | .fence .release, .store _ _ => true  -- Release → St
    | .fence .release, .fence .release => true  -- Release → Release
    | .fence .release, .fence .full => true     -- Release → Full
    -- Release → Ld is False
    -- Release → Acquire is False (key difference from WMM!)
    -- Acquire fence orderings (orders everything after it)
    | .fence .acquire, .load _ _ => true   -- Acquire → Ld
    | .fence .acquire, .store _ _ => true  -- Acquire → St
    | .fence .acquire, .fence .release => true  -- Acquire → Release
    | .fence .acquire, .fence .acquire => true  -- Acquire → Acquire
    | .fence .acquire, .fence .full => true     -- Acquire → Full
    -- Full fence orderings (orders everything)
    | .fence .full, .load _ _ => true      -- Full → Ld
    | .fence .full, .store _ _ => true     -- Full → St
    | .fence .full, .fence .release => true     -- Full → Release
    | .fence .full, .fence .acquire => true     -- Full → Acquire
    | .fence .full, .fence .full => true        -- Full → Full
    -- Everything else is relaxed
    | _, _ => false
  memFenceOnly := by
    intro i1 i2 h_ord
    match h_t1 : i1.instType, h_t2 : i2.instType with
    | .load _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .store _ _, .fence _ =>
      constructor
      · left; simp [Instruction.isMemInst, h_t1]
      · right; simp [Instruction.isFence, h_t2]
    | .fence _, .load _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .store _ _ =>
      constructor
      · right; simp [Instruction.isFence, h_t1]
      · left; simp [Instruction.isMemInst, h_t2]
    | .fence _, .fence _ =>
      constructor <;> (right; simp [Instruction.isFence, h_t1, h_t2])
    | .load _ _, .load _ _ | .load _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .load _ _, .regOp _ _ _ | .load _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .load _ _ | .store _ _, .store _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .store _ _, .regOp _ _ _ | .store _ _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .fence _, .regOp _ _ _ | .fence _, .branch _ _ =>
      simp [h_t1, h_t2] at h_ord
    | .regOp _ _ _, _ | .branch _ _, _ =>
      simp [h_t1] at h_ord

/-- ARM is NOT I2E compatible (allows Load-Store reordering) -/
theorem orderedARM_not_isI2ECompatible : ¬orderedARM.isI2ECompatible := by
  intro h_compat
  simp [OrderedFunc.isI2ECompatible] at h_compat
  let i_load : Instruction := ⟨(0 : Nat), (0 : Nat), .load (.literal (0 : Nat)) (0 : Nat)⟩
  let i_store : Instruction := ⟨(1 : Nat), (0 : Nat), .store (.literal (1 : Nat)) (.literal (0 : Nat))⟩
  have h := h_compat i_load i_store
  simp [Instruction.isLoad, Instruction.isStore] at h
  have h_false : orderedARM.ordered i_load i_store = false := by
    simp [orderedARM, i_load, i_store]
  simp [h_false] at h

/-- RISC-V is NOT I2E compatible (allows Load-Store reordering) -/
theorem orderedRISCV_not_isI2ECompatible : ¬orderedRISCV.isI2ECompatible := by
  intro h_compat
  simp [OrderedFunc.isI2ECompatible] at h_compat
  let i_load : Instruction := ⟨(0 : Nat), (0 : Nat), .load (.literal (0 : Nat)) (0 : Nat)⟩
  let i_store : Instruction := ⟨(1 : Nat), (0 : Nat), .store (.literal (1 : Nat)) (.literal (0 : Nat))⟩
  have h := h_compat i_load i_store
  simp [Instruction.isLoad, Instruction.isStore] at h
  have h_false : orderedRISCV.ordered i_load i_store = false := by
    simp [orderedRISCV, i_load, i_store]
  simp [h_false] at h

end GamI2e
