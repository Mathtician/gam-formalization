/-
Basic relations for the GAM/I2E memory model formalization.

This module defines the fundamental relations used in both
axiomatic and operational models:
- Program order
- Dependency relations
- Memory order
- Read-from relations

All relations that depend on memory addresses are parameterized by an
`AddressAssignment`, which maps instruction IDs to their computed addresses.
This allows the model to handle both literal addresses and register-computed
addresses uniformly.
-/

import GamI2e.Types

namespace GamI2e

/-- A binary relation on instructions -/
def Relation := Instruction → Instruction → Prop

/-- Program order: per-processor total order of instructions
    i1 <_po i2 means i1 comes before i2 in the same processor -/
structure ProgramOrder where
  rel : Relation
  -- Same processor requirement
  sameProc : ∀ i1 i2, rel i1 i2 → i1.procId = i2.procId
  -- Irreflexive
  irrefl : ∀ i, ¬rel i i
  -- Transitive
  trans : ∀ i1 i2 i3, rel i1 i2 → rel i2 i3 → rel i1 i3
  -- Total within each processor
  total : ∀ i1 i2, i1.procId = i2.procId → i1 ≠ i2 → rel i1 i2 ∨ rel i2 i1

/-- Data dependency: i1 <_ddep i2 if i2 reads a register written by i1 -/
def dataDep (po : ProgramOrder) (i1 i2 : Instruction) : Prop :=
  po.rel i1 i2 ∧
  ∃ r ∈ i1.writeSet, r ∈ i2.readSet ∧
  -- No intervening write to r
  ¬∃ i, po.rel i1 i ∧ po.rel i i2 ∧ r ∈ i.writeSet

/-- Address dependency: i1 <_adep i2 if i2 is a memory instruction
    that uses a register written by i1 for address computation -/
def addrDep (po : ProgramOrder) (i1 i2 : Instruction) : Prop :=
  po.rel i1 i2 ∧
  ∃ r ∈ i1.writeSet, r ∈ i2.addrReadSet ∧
  -- No intervening write to r
  ¬∃ i, po.rel i1 i ∧ po.rel i i2 ∧ r ∈ i.writeSet

/-- Address dependency implies data dependency.

    This follows from the ISA property that ARS(I) ⊆ RS(I) for all instructions,
    i.e., registers used for address computation must be in the read set.
    The paper states: "data-dependency includes addr-dependency".

    We use the axiom addrReadSet_subset_readSet from Types.lean. -/
theorem addrDep_implies_dataDep (po : ProgramOrder) (i1 i2 : Instruction) :
    addrDep po i1 i2 → dataDep po i1 i2 :=
  fun h =>
    let ⟨h_po, r, h_write, h_addr, h_no_intervene⟩ := h
    ⟨h_po, r, h_write,
     -- h_addr : r ∈ i2.addrReadSet
     -- By axiom, this implies r ∈ i2.readSet
     addrReadSet_subset_readSet i2 r h_addr,
     h_no_intervene⟩

/-- Memory order: total order of all memory instructions
    i1 <_mo i2 means i1 is globally ordered before i2 -/
structure MemoryOrder where
  rel : Relation
  -- Only relates memory instructions
  memOnly : ∀ i1 i2, rel i1 i2 → i1.isMemInst ∧ i2.isMemInst
  -- Irreflexive
  irrefl : ∀ i, ¬rel i i
  -- Transitive
  trans : ∀ i1 i2 i3, rel i1 i2 → rel i2 i3 → rel i1 i3
  -- Total over all memory instructions
  total : ∀ i1 i2, i1.isMemInst → i2.isMemInst → i1 ≠ i2 →
          rel i1 i2 ∨ rel i2 i1

/-- Read-from relation parameterized by address assignment.
    Relates a store to a load that reads from it. -/
structure ReadFrom (aa : AddressAssignment) where
  rel : Relation
  -- Store to load
  storeToLoad : ∀ s l, rel s l → s.isStore ∧ l.isLoad
  -- Same address via address assignment
  sameAddr : ∀ s l, rel s l → s.sameAddrWith aa l
  -- Functional: each load reads from at most one store
  functional : ∀ l s1 s2, rel s1 l → rel s2 l → s1 = s2
  -- Coverage: each load reads from exactly one store
  -- (Every load instruction has a source store)
  coverage : ∀ l, l.isLoad → (aa l.id).isSome → ∃ s, rel s l

/-- Coherence order (per-address): total order of stores to a specific address -/
def coherenceOrder (aa : AddressAssignment) (mo : MemoryOrder) (a : Addr) : Relation :=
  fun s1 s2 =>
    s1.isStore ∧ s2.isStore ∧
    aa s1.id = some a ∧ aa s2.id = some a ∧
    mo.rel s1 s2

/-- Coherence order flattened across all addresses -/
def coherenceOrderAll (aa : AddressAssignment) (mo : MemoryOrder) : Relation :=
  fun s1 s2 =>
    s1.isStore ∧ s2.isStore ∧
    s1.sameAddrWith aa s2 ∧
    mo.rel s1 s2

/-- From-reads relation: l fr s means l reads from some store s',
    and s comes after s' in coherence order. -/
def fromReads (aa : AddressAssignment) (rf : ReadFrom aa) (mo : MemoryOrder) : Relation :=
  fun l s =>
    l.isLoad ∧ s.isStore ∧
    ∃ s', rf.rel s' l ∧
    s'.sameAddrWith aa s ∧
    mo.rel s' s

/-- Program order restricted to same location (memory instructions only)

The paper's poloc relation implicitly only relates memory accesses at the same
address. We make this explicit by requiring both instructions to be memory
instructions (loads or stores). This ensures that poloc edges in cycles
necessarily involve memory instructions, which is needed for the SC-per-Location
proof's case analysis. -/
def programOrderLoc (aa : AddressAssignment) (po : ProgramOrder) : Relation :=
  fun i1 i2 => po.rel i1 i2 ∧ i1.sameAddrWith aa i2 ∧ i1.isMemInst ∧ i2.isMemInst

/-- Read-from external (different processors) -/
def readFromExternal (aa : AddressAssignment) (rf : ReadFrom aa) : Relation :=
  fun s l => rf.rel s l ∧ s.procId ≠ l.procId

/-- Read-from internal (same processor) -/
def readFromInternal (aa : AddressAssignment) (rf : ReadFrom aa) : Relation :=
  fun s l => rf.rel s l ∧ s.procId = l.procId

/-- Acyclicity check for a relation -/
def acyclic (r : Relation) : Prop :=
  ∀ i, ¬(Relation.TransGen r i i)

/-- Union of two relations -/
def unionRel (r1 r2 : Relation) : Relation :=
  fun i1 i2 => r1 i1 i2 ∨ r2 i1 i2

/-- Composition of two relations -/
def composeRel (r1 r2 : Relation) : Relation :=
  fun i1 i2 => ∃ i, r1 i1 i ∧ r2 i i2

/-- Inverse of a relation -/
def inverseRel (r : Relation) : Relation :=
  fun i1 i2 => r i2 i1

/-- Reflexive transitive closure (r*) -/
def reflTransClosure (r : Relation) : Relation :=
  fun i1 i2 => i1 = i2 ∨ Relation.TransGen r i1 i2

/-- Transitive closure (r+) - at least one step -/
def transClosure (r : Relation) : Relation :=
  fun i1 i2 => Relation.TransGen r i1 i2

notation:50 r1 " ∪ᵣ " r2 => unionRel r1 r2
notation:60 r1 " ;ᵣ " r2 => composeRel r1 r2
notation:70 r "⁻¹" => inverseRel r

end GamI2e
