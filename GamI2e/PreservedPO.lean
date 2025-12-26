/-
Preserved Program Order (ppo) for GAM/I2E.

This module defines the preserved program order, which captures
the constraints on out-of-order execution. The ppo is computed from
the program order and consists of three parts:
1. Preserved memory/fence order (based on Ordered function)
2. Preserved dependency order
3. Preserved same-address order

All relations that depend on memory addresses are parameterized by an
`AddressAssignment`, which maps instruction IDs to their computed addresses.
-/

import GamI2e.Types
import GamI2e.Relations
import GamI2e.Ordering

namespace GamI2e

/-- Preserved memory/fence order: <_ppomf
    (Definition 1 in paper, Section 3.1.1)

    Note: This relation does not depend on addresses, so it doesn't need
    the AddressAssignment parameter. -/
def preservedMemFenceOrder (of : OrderedFunc) (po : ProgramOrder) : Relation :=
  fun i1 i2 =>
    (i1.isMemInst ∨ i1.isFence) ∧
    (i2.isMemInst ∨ i2.isFence) ∧
    po.rel i1 i2 ∧
    of.ordered i1 i2 = true

/-- Preserved dependency order: <_ppod
    (Definition 5 in paper, Section 3.1.1)

    This includes:
    1. Data dependencies
    2. Branch to store dependencies
    3. Address dependency + program order to store
    4. Data dependency to same-address load -/
def preservedDepOrder (aa : AddressAssignment) (po : ProgramOrder) : Relation :=
  fun i1 i2 =>
    -- Case 1: Data dependency (no address check needed)
    dataDep po i1 i2 ∨
    -- Case 2: Branch before store (no address check needed)
    (i1.isBranch ∧ i2.isStore ∧ po.rel i1 i2) ∨
    -- Case 3: Address dependency + po to store (no address check needed for this case)
    (i2.isStore ∧
     ∃ im, im.isMemInst ∧ addrDep po i1 im ∧ po.rel im i2) ∨
    -- Case 4: Data dependency to same-address load via store (uses address assignment)
    (i2.isLoad ∧
     ∃ s, s.isStore ∧ s.sameAddrWith aa i2 ∧
     dataDep po i1 s ∧ po.rel s i2 ∧
     -- No intervening store to same address
     ¬∃ s', s'.isStore ∧ s'.sameAddrWith aa i2 ∧ po.rel s s' ∧ po.rel s' i2)

/-- Preserved same-address order: <_pposa
    (Definition 6 in paper, Section 3.1.1)

    This includes:
    1. Load to store to same address
    2. Store to store to same address
    3. Load to load to same address (no intervening store) -/
def preservedSameAddrOrder (aa : AddressAssignment) (po : ProgramOrder) : Relation :=
  fun i1 i2 =>
    -- Case 1: Load to store, same address
    (i1.isLoad ∧ i2.isStore ∧ po.rel i1 i2 ∧ i1.sameAddrWith aa i2) ∨
    -- Case 2: Store to store, same address
    (i1.isStore ∧ i2.isStore ∧ po.rel i1 i2 ∧ i1.sameAddrWith aa i2) ∨
    -- Case 3: Load to load, same address, no intervening store
    (i1.isLoad ∧ i2.isLoad ∧ po.rel i1 i2 ∧ i1.sameAddrWith aa i2 ∧
     ¬∃ s, s.isStore ∧ s.sameAddrWith aa i1 ∧ po.rel i1 s ∧ po.rel s i2)

/-- Preserved program order: <_ppo
    (Definition 7 in paper, Section 3.1.1)

    This is the transitive closure of the union of:
    - Preserved memory/fence order
    - Preserved dependency order
    - Preserved same-address order -/
def preservedProgramOrder (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) : Relation :=
  Relation.TransGen (
    preservedMemFenceOrder of po ∪ᵣ
    preservedDepOrder aa po ∪ᵣ
    preservedSameAddrOrder aa po
  )

-- Notation
notation:50 "ppo[" aa "," of "," po "]" => preservedProgramOrder aa of po
notation:50 "ppomf[" of "," po "]" => preservedMemFenceOrder of po
notation:50 "ppod[" aa "," po "]" => preservedDepOrder aa po
notation:50 "pposa[" aa "," po "]" => preservedSameAddrOrder aa po

/-- Helper: extract po from a single ppo base edge -/
private theorem ppo_base_implies_po (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder)
    (i1 i2 : Instruction)
    (h : (preservedMemFenceOrder of po ∪ᵣ preservedDepOrder aa po ∪ᵣ preservedSameAddrOrder aa po) i1 i2) :
    po.rel i1 i2 := by
  rcases h with h_mf | h_dep | h_sa
  · exact h_mf.2.2.1
  · rcases h_dep with h_data | h_br | h_adep | h_same
    · exact h_data.1
    · exact h_br.2.2
    · obtain ⟨_, im, _, h_adep_im, h_po_im⟩ := h_adep
      exact po.trans _ _ _ h_adep_im.1 h_po_im
    · obtain ⟨_, s, _, _, h_data_s, h_po_s, _⟩ := h_same
      exact po.trans _ _ _ h_data_s.1 h_po_s
  · rcases h_sa with h_ld_st | h_st_st | h_ld_ld
    · exact h_ld_st.2.2.1
    · exact h_st_st.2.2.1
    · exact h_ld_ld.2.2.1

/-- If i1 <_ppo i2 then i1 <_po i2 -/
theorem ppo_implies_po (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) :
    ∀ i1 i2, preservedProgramOrder aa of po i1 i2 → po.rel i1 i2 := by
  intro i1 i2 h
  induction h with
  | single h_base => exact ppo_base_implies_po aa of po _ _ h_base
  | tail _ h_last ih => exact po.trans _ _ _ ih (ppo_base_implies_po aa of po _ _ h_last)

/-- ppo is irreflexive (follows from po being irreflexive) -/
theorem ppo_irrefl (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) :
    ∀ i, ¬preservedProgramOrder aa of po i i := by
  intro i h
  have := ppo_implies_po aa of po i i h
  exact po.irrefl i this

/-- ppo is transitive (by definition as TransGen) -/
theorem ppo_trans (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) :
    ∀ i1 i2 i3,
    preservedProgramOrder aa of po i1 i2 →
    preservedProgramOrder aa of po i2 i3 →
    preservedProgramOrder aa of po i1 i3 := by
  intro i1 i2 i3 h1 h2
  exact Relation.TransGen.trans h1 h2

/-- If ordered returns true, then ppomf edge exists -/
theorem ordered_implies_ppomf (of : OrderedFunc) (po : ProgramOrder) :
    ∀ i1 i2,
    (i1.isMemInst ∨ i1.isFence) →
    (i2.isMemInst ∨ i2.isFence) →
    po.rel i1 i2 →
    of.ordered i1 i2 = true →
    preservedMemFenceOrder of po i1 i2 := by
  intro i1 i2 h1 h2 h_po h_ord
  exact ⟨h1, h2, h_po, h_ord⟩

/-- Data dependency implies ppod edge -/
theorem dataDep_implies_ppod (aa : AddressAssignment) (po : ProgramOrder) :
    ∀ i1 i2, dataDep po i1 i2 → preservedDepOrder aa po i1 i2 := by
  intro i1 i2 h
  left
  exact h

/-- Same-address store-store implies pposa edge -/
theorem stSt_sameAddr_implies_pposa (aa : AddressAssignment) (po : ProgramOrder) :
    ∀ s1 s2,
    s1.isStore →
    s2.isStore →
    po.rel s1 s2 →
    s1.sameAddrWith aa s2 →
    preservedSameAddrOrder aa po s1 s2 := by
  intro s1 s2 h1 h2 h_po h_same
  right
  left
  exact ⟨h1, h2, h_po, h_same⟩

/-- Components of ppo are included in ppo -/
theorem ppomf_subset_ppo (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) :
    ∀ i1 i2, preservedMemFenceOrder of po i1 i2 → preservedProgramOrder aa of po i1 i2 := by
  intro i1 i2 h
  apply Relation.TransGen.single
  left
  exact h

theorem ppod_subset_ppo (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) :
    ∀ i1 i2, preservedDepOrder aa po i1 i2 → preservedProgramOrder aa of po i1 i2 := by
  intro i1 i2 h
  apply Relation.TransGen.single
  right
  left
  exact h

theorem pposa_subset_ppo (aa : AddressAssignment) (of : OrderedFunc) (po : ProgramOrder) :
    ∀ i1 i2, preservedSameAddrOrder aa po i1 i2 → preservedProgramOrder aa of po i1 i2 := by
  intro i1 i2 h
  apply Relation.TransGen.single
  right
  right
  exact h

end GamI2e
