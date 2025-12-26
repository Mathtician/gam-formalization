/-
GAM Operational Model

This module defines the operational semantics of GAM using a
ROB (Reorder Buffer) based abstract machine with speculative execution.

Key components:
- ROB: Reorder buffer holding instructions
- Monolithic memory
- Speculative execution with kill mechanism
- Ghost states for proof purposes
-/

import GamI2e.Types
import GamI2e.Relations
import GamI2e.Ordering
import GamI2e.PreservedPO
import GamI2e.Axiomatic

namespace GamI2e

/-- Register file: mapping from register IDs to values -/
def RegisterFile := RegId → Value

/-- Memory state: mapping from addresses to values -/
def Memory := Addr → Value

/-- Compute the concrete address from an AddrOperand given a register file -/
def AddrOperand.compute (ao : AddrOperand) (regs : RegisterFile) : Addr :=
  match ao with
  | .literal a => a
  | .regOffset r offset => Nat.add (regs r) offset
  | .regSum r1 r2 offset => Nat.add (Nat.add (regs r1) (regs r2)) offset

/-- ROB entry state -/
structure ROBEntry where
  /-- The instruction -/
  inst : Instruction
  /-- Whether the instruction is marked as done -/
  done : Bool
  /-- Whether the address has been computed (for memory instructions) -/
  addrAvailable : Bool
  /-- Computed address (if addrAvailable) -/
  addr? : Option Addr
  /-- Computed result value (for non-memory instructions and loads) -/
  result? : Option Value
  /-- Computed store data (for stores) -/
  storeData? : Option Value
  /-- Predicted branch target (for branches) -/
  predictedTarget? : Option Addr

  -- Ghost states (for proofs only, not observable)
  /-- Timestamp when instruction was marked done -/
  doneTS : Option Nat
  /-- Timestamp when address was computed -/
  addrTS : Option Nat
  /-- Timestamp when store data was computed -/
  stDataTS : Option Nat
  /-- Store that this load reads from (for loads) -/
  fromStore? : Option InstId

/-- Well-formedness predicate for ROBEntry.
    This captures invariants maintained by the operational semantics:
    - Done memory instructions must have their address available
    - If address is available, addr? must be Some -/
def ROBEntry.wellFormed (entry : ROBEntry) : Prop :=
  -- If a memory instruction is done, its address must be available
  (entry.inst.isMemInst ∧ entry.done → entry.addrAvailable) ∧
  -- If address is available, addr? must be Some
  (entry.addrAvailable → entry.addr?.isSome)

/-- ROB: ordered list of entries (oldest first) -/
def ROB := List ROBEntry

/-- Membership instance for ROB (since it's a type alias for List) -/
instance : Membership ROBEntry ROB where
  mem robList e := List.Mem e robList

/-- Processor state -/
structure ProcessorState where
  /-- Processor ID -/
  id : ProcId
  /-- Reorder buffer -/
  rob : ROB
  /-- Program counter -/
  pc : Addr
  /-- Register file (architectural state) -/
  regs : RegisterFile

/-- Global state of the operational model -/
structure OperationalState where
  /-- Current global timestamp (for ghost state tracking) -/
  globalTime : Nat
  /-- Monolithic shared memory -/
  mem : Memory
  /-- Per-processor state -/
  processors : ProcId → ProcessorState
  /-- Number of processors -/
  numProcs : Nat

/-- Well-formedness predicate for OperationalState.
    All ROB entries across all processors are well-formed. -/
def OperationalState.wellFormed (state : OperationalState) : Prop :=
  ∀ p, ∀ entry, entry ∈ (state.processors p).rob → entry.wellFormed

/-- Check if an operand is ready in the ROB
    An operand is ready if there's no older instruction writing to that register,
    or the oldest such instruction is done -/
def ROB.operandReady (rob : ROB) (entry : ROBEntry) (reg : RegId) : Bool :=
  -- Find all older instructions (before entry) that write to this register
  let olderWriters := rob.filter (fun e =>
    e.inst.writeSet.contains reg &&
    (e.inst.id : Nat) < (entry.inst.id : Nat))
  -- All such instructions must be done
  olderWriters.all (fun e => e.done)

/-- Check if all operands of an instruction are ready -/
def ROB.allOperandsReady (rob : ROB) (entry : ROBEntry) : Bool :=
  -- Check that all registers in the read set are ready
  entry.inst.readSet.all (fun reg => rob.operandReady entry reg)

/-- Check if an instruction can be executed based on ordering constraints -/
def ROB.canExecute (of : OrderedFunc) (rob : ROB) (entry : ROBEntry) : Bool :=
  -- Check that all older instructions that must complete before this one are done
  let olderInsts := rob.filter (fun e => (e.inst.id : Nat) < (entry.inst.id : Nat))
  olderInsts.all (fun older =>
    -- If ordering constraint exists from older to current, older must be done
    if of.ordered older.inst entry.inst then
      older.done
    else
      true)

/-- Find an entry in the ROB by instruction ID -/
def ROB.findEntry (rob : ROB) (instId : InstId) : Option ROBEntry :=
  rob.find? (fun e => e.inst.id == instId)

/-- Update an entry in the ROB -/
def ROB.updateEntry (rob : ROB) (instId : InstId) (f : ROBEntry → ROBEntry) : ROB :=
  rob.map (fun e => if e.inst.id == instId then f e else e)

/-- Check if ROB is at capacity -/
def ROB.isFull (rob : ROB) (maxSize : Nat) : Bool :=
  rob.length >= maxSize

/-- Execution rules (one per instruction type) -/
inductive ExecutionRule where
  | fetch : ExecutionRule
  | executeRegToReg : InstId → ExecutionRule
  | executeBranch : InstId → ExecutionRule
  | executeFence : InstId → ExecutionRule
  | executeLoad : InstId → ExecutionRule
  | computeStoreData : InstId → ExecutionRule
  | executeStore : InstId → ExecutionRule
  | computeMemAddr : InstId → ExecutionRule

/-- Result of executing a rule -/
structure ExecutionResult where
  /-- New global state -/
  newState : OperationalState
  /-- Whether any instruction was killed -/
  killed : List InstId

/-- Check if a rule can be applied to the current state -/
def ExecutionRule.guard (_of : OrderedFunc) (rule : ExecutionRule)
    (_state : OperationalState) (_procId : ProcId) : Bool :=
  match rule with
  | fetch => true  -- Can always fetch
  | executeRegToReg _ => true  -- TODO: Proper guard
  | executeBranch _ => true  -- TODO: Proper guard
  | executeFence _ => true  -- TODO: Proper guard
  | executeLoad _ => true  -- TODO: Proper guard
  | computeStoreData _ => true  -- TODO: Proper guard
  | executeStore _ => true  -- TODO: Proper guard
  | computeMemAddr _ => true  -- TODO: Proper guard

/-- Apply an execution rule (transition function) -/
def ExecutionRule.apply (of : OrderedFunc) (rule : ExecutionRule)
    (state : OperationalState) (procId : ProcId) : Option ExecutionResult :=
  let proc := state.processors procId
  match rule with
  | fetch =>
      -- Fetch: Add new instruction to ROB
      -- Simplified: just create a placeholder entry
      let newEntry : ROBEntry := {
        inst := { id := state.globalTime, procId := procId, instType := .fence .full }  -- Placeholder
        done := false
        addrAvailable := false
        addr? := none
        result? := none
        storeData? := none
        predictedTarget? := none
        doneTS := none
        addrTS := none
        stDataTS := none
        fromStore? := none
      }
      let newPC : Addr := Nat.add proc.pc 1
      let newProc : ProcessorState := { proc with
        rob := List.append proc.rob [newEntry]
        pc := newPC
      }
      let newState : OperationalState := { state with
        processors := fun p => if p == procId then newProc else state.processors p
        globalTime := state.globalTime + (1 : Nat)
      }
      some { newState := newState, killed := [] }

  | executeRegToReg instId =>
      -- Execute register-to-register operation
      match proc.rob.findEntry instId with
      | none => none
      | some entry =>
          match entry.inst.instType with
          | .regOp _ _ _ =>
              if !proc.rob.allOperandsReady entry then
                none
              else
                -- Mark as done and compute result (simplified: just store 0)
                let newRob := proc.rob.updateEntry instId (fun e =>
                  { e with done := true, result? := some (0 : Nat), doneTS := some state.globalTime })
                let newProc := { proc with rob := newRob }
                let newState : OperationalState := { state with
                  processors := fun p => if p == procId then newProc else state.processors p
                  globalTime := state.globalTime + 1
                }
                some { newState := newState, killed := [] }
          | _ => none

  | executeFence instId =>
      -- Execute fence: mark as done
      match proc.rob.findEntry instId with
      | none => none
      | some entry =>
          if !entry.inst.isFence then none
          else if !proc.rob.canExecute of entry then none
          else
            let newRob := proc.rob.updateEntry instId (fun e =>
              { e with done := true, doneTS := some state.globalTime })
            let newProc := { proc with rob := newRob }
            let newState := { state with
              processors := fun p => if p == procId then newProc else state.processors p
              globalTime := state.globalTime + 1
            }
            some { newState := newState, killed := [] }

  | executeBranch instId =>
      -- Execute branch: mark as done, potentially update PC (simplified: no misprediction handling)
      match proc.rob.findEntry instId with
      | none => none
      | some entry =>
          match entry.inst.instType with
          | .branch _ _target =>
              if !proc.rob.allOperandsReady entry then none
              else if !proc.rob.canExecute of entry then none
              else
                -- Mark as done (simplified: assume branch always taken)
                let newRob := proc.rob.updateEntry instId (fun e =>
                  { e with done := true, doneTS := some state.globalTime })
                let newProc := { proc with rob := newRob }
                let newState := { state with
                  processors := fun p => if p == procId then newProc else state.processors p
                  globalTime := state.globalTime + 1
                }
                some { newState := newState, killed := [] }
          | _ => none

  | computeMemAddr instId =>
      -- Compute memory address for load/store
      match proc.rob.findEntry instId with
      | none => none
      | some entry =>
          if entry.addrAvailable then none  -- Already computed
          else
            match entry.inst.instType with
            | .load addrOp _ | .store addrOp _ =>
                if !proc.rob.allOperandsReady entry then none
                else
                  -- Compute the concrete address from the operand
                  let computedAddr := addrOp.compute proc.regs
                  let newRob := proc.rob.updateEntry instId (fun e =>
                    { e with
                      addrAvailable := true
                      addr? := some computedAddr
                      addrTS := some state.globalTime
                    })
                  let newProc := { proc with rob := newRob }
                  let newState := { state with
                    processors := fun p => if p == procId then newProc else state.processors p
                    globalTime := state.globalTime + 1
                  }
                  some { newState := newState, killed := [] }
            | _ => none

  | executeLoad instId =>
      -- Execute load: read from memory
      match proc.rob.findEntry instId with
      | none => none
      | some entry =>
          match entry.inst.instType with
          | .load _addrOp _destReg =>
              if !entry.addrAvailable then none
              else if !proc.rob.canExecute of entry then none
              else
                -- Read from memory using the computed address
                match entry.addr? with
                | none => none  -- Address should be available
                | some addr =>
                  let value := state.mem addr
                  let newRob := proc.rob.updateEntry instId (fun e =>
                    { e with
                      done := true
                      result? := some value
                      doneTS := some state.globalTime
                    })
                  let newProc := { proc with rob := newRob }
                  let newState := { state with
                    processors := fun p => if p == procId then newProc else state.processors p
                    globalTime := state.globalTime + 1
                  }
                  some { newState := newState, killed := [] }
          | _ => none

  | computeStoreData instId =>
      -- Compute store data value
      match proc.rob.findEntry instId with
      | none => none
      | some entry =>
          match entry.inst.instType with
          | .store _addrOp dataOp =>
              if entry.storeData?.isSome then none  -- Already computed
              else if !proc.rob.allOperandsReady entry then none
              else
                -- Compute the concrete value from the operand
                let computedValue := match dataOp with
                  | .literal v => v
                  | .register r => proc.regs r
                let newRob := proc.rob.updateEntry instId (fun e =>
                  { e with
                    storeData? := some computedValue
                    stDataTS := some state.globalTime
                  })
                let newProc := { proc with rob := newRob }
                let newState := { state with
                  processors := fun p => if p == procId then newProc else state.processors p
                  globalTime := state.globalTime + 1
                }
                some { newState := newState, killed := [] }
          | _ => none

  | executeStore instId =>
      -- Execute store: write to memory
      match proc.rob.findEntry instId with
      | none => none
      | some entry =>
          match entry.inst.instType with
          | .store _addrOp _dataOp =>
              if !entry.addrAvailable then none
              else if entry.storeData?.isNone then none
              else if !proc.rob.canExecute of entry then none
              else
                -- Write to memory using computed address and data
                match entry.addr?, entry.storeData? with
                | some addr, some storeValue =>
                    let newMem := fun a => if a == addr then storeValue else state.mem a
                    let newRob := proc.rob.updateEntry instId (fun e =>
                      { e with done := true, doneTS := some state.globalTime })
                    let newProc := { proc with rob := newRob }
                    let newState := { state with
                      mem := newMem
                      processors := fun p => if p == procId then newProc else state.processors p
                      globalTime := state.globalTime + 1
                    }
                    some { newState := newState, killed := [] }
                | _, _ => none  -- Address or data not available
          | _ => none

/-- One step of execution: pick a processor and a rule, then apply it -/
def step (of : OrderedFunc) (state : OperationalState)
    (procId : ProcId) (rule : ExecutionRule) : Option OperationalState :=
  if rule.guard of state procId then
    (rule.apply of state procId).map (·.newState)
  else
    none

/-- Multi-step execution: trace of states -/
def Trace := List OperationalState

/-- Check if a trace is a valid execution -/
def validTrace (of : OrderedFunc) (trace : Trace) : Prop :=
  match trace with
  | [] => False
  | [_] => True
  | s1 :: s2 :: rest =>
    (∃ p rule, step of s1 p rule = some s2) ∧
    validTrace of (s2 :: rest)

/-! ## Address Assignment Extraction

The following functions extract an `AddressAssignment` from the operational model state.
This allows connecting the operational model to the axiomatic model by providing
the computed addresses for all memory instructions.
-/

/-- Find a ROB entry by instruction ID across all processors -/
def OperationalState.findROBEntry (state : OperationalState) (instId : InstId) : Option ROBEntry :=
  -- Search all processors' ROBs for the entry
  let entries := (List.range state.numProcs).filterMap (fun p =>
    (state.processors p).rob.find? (fun e => e.inst.id == instId))
  entries.head?

/-- Helper: if head? returns some, the element is in the list -/
theorem List.head?_mem {α : Type _} (l : List α) (x : α) :
    l.head? = some x → x ∈ l := by
  intro h
  cases l with
  | nil => simp at h
  | cons hd tl =>
    simp [List.head?] at h
    simp [h]

/-- If findROBEntry returns some entry, then that entry is in some processor's ROB -/
theorem OperationalState.findROBEntry_mem (state : OperationalState) (instId : InstId) (entry : ROBEntry) :
    state.findROBEntry instId = some entry →
    ∃ p, p < state.numProcs ∧ entry ∈ (state.processors p).rob := by
  intro h_find
  unfold findROBEntry at h_find
  -- h_find tells us that entries.head? = some entry where entries is the filterMap result
  -- This means entries is nonempty and entry is from some processor's ROB
  -- The proof requires showing that head? = some implies the element came from the filterMap
  -- which in turn came from some p's ROB via find?

  -- Extract that entry is in the filterMap result
  have h_in_entries : entry ∈ (List.range state.numProcs).filterMap (fun p =>
      (state.processors p).rob.find? (fun e => e.inst.id == instId)) :=
    List.head?_mem _ _ h_find

  -- Use filterMap membership to get the processor
  rw [List.mem_filterMap] at h_in_entries
  obtain ⟨p, hp_in_range, hp_find⟩ := h_in_entries

  -- p ∈ List.range state.numProcs means p < state.numProcs
  -- Note: ProcId = Nat, so we need to handle the coercion carefully
  have hp_bound : p < state.numProcs := by
    have h := List.mem_range.mp hp_in_range
    exact h

  -- find? returning some means entry is in that processor's ROB
  have h_entry_in_rob : entry ∈ (state.processors p).rob :=
    List.mem_of_find?_eq_some hp_find

  exact ⟨p, hp_bound, h_entry_in_rob⟩

/-- Extract an address assignment from the operational state.
    Returns the computed address for each instruction that has one. -/
def OperationalState.addressAssignment (state : OperationalState) : AddressAssignment :=
  fun instId =>
    match state.findROBEntry instId with
    | some entry =>
      if entry.addrAvailable then entry.addr?
      else none
    | none => none

/-- The address assignment covers all done memory instructions.
    This requires the state to be well-formed (invariant maintained by operational semantics). -/
theorem OperationalState.addressAssignment_covers_done
    (state : OperationalState) (instId : InstId)
    (h_wf : state.wellFormed) :
    (∃ entry, state.findROBEntry instId = some entry ∧ entry.done ∧ entry.inst.isMemInst) →
    (state.addressAssignment instId).isSome := by
  intro ⟨entry, h_find, h_done, h_mem⟩
  unfold addressAssignment
  simp [h_find]
  -- Need to show: (if entry.addrAvailable then entry.addr? else none).isSome
  -- From well-formedness: entry.done ∧ entry.inst.isMemInst → entry.addrAvailable
  -- And: entry.addrAvailable → entry.addr?.isSome

  -- Use helper lemma to get entry's ROB membership
  obtain ⟨p, _h_p_bound, h_entry_in_rob⟩ := findROBEntry_mem state instId entry h_find

  -- Get well-formedness for this entry
  have h_entry_wf := h_wf p entry h_entry_in_rob

  -- From wellFormed: (entry.inst.isMemInst ∧ entry.done → entry.addrAvailable)
  have h_addr_avail : entry.addrAvailable = true := by
    have h1 := h_entry_wf.1  -- entry.inst.isMemInst ∧ entry.done → entry.addrAvailable
    have h_combined : entry.inst.isMemInst = true ∧ entry.done = true := ⟨h_mem, h_done⟩
    exact h1 h_combined

  simp [h_addr_avail]

  -- From wellFormed: entry.addrAvailable → entry.addr?.isSome
  have h_addr_some := h_entry_wf.2 h_addr_avail
  exact h_addr_some

/-- Extract the program order from the final operational state.
    Instructions in the same ROB are ordered by their position. -/
def OperationalState.extractProgramOrder (state : OperationalState) : Relation :=
  fun i1 i2 =>
    i1.procId = i2.procId ∧
    ∃ (idx1 idx2 : Nat),
      let rob : List ROBEntry := (state.processors i1.procId).rob
      (∃ entry1 : ROBEntry, rob[idx1]? = some entry1 ∧ entry1.inst = i1) ∧
      (∃ entry2 : ROBEntry, rob[idx2]? = some entry2 ∧ entry2.inst = i2) ∧
      idx1 < idx2

/-- Extract the memory order from the final operational state.
    Memory instructions are ordered by their doneTS timestamps. -/
def OperationalState.extractMemoryOrder (state : OperationalState) : Relation :=
  fun i1 i2 =>
    i1.isMemInst ∧ i2.isMemInst ∧
    ∃ entry1 entry2,
      state.findROBEntry i1.id = some entry1 ∧
      state.findROBEntry i2.id = some entry2 ∧
      entry1.done ∧ entry2.done ∧
      match entry1.doneTS, entry2.doneTS with
      | some ts1, some ts2 => ts1 < ts2
      | _, _ => False

/-- Extract the read-from relation from the final operational state.
    A store reads from a load if the load's fromStore? field points to the store. -/
def OperationalState.extractReadFrom (state : OperationalState) : Relation :=
  fun s l =>
    s.isStore ∧ l.isLoad ∧
    ∃ entryL,
      state.findROBEntry l.id = some entryL ∧
      entryL.fromStore? = some s.id

/-- Build a complete execution witness from the final operational state -/
def OperationalState.toExecutionWitness (_state : OperationalState) : Option ExecutionWitness :=
  -- This would construct a full ExecutionWitness from the operational state
  -- The implementation requires proving various properties about the state
  none  -- Placeholder

/-- Key theorem: The address assignment extracted from a completed operational execution
    is consistent with the computed addresses in the ROB entries -/
theorem OperationalState.addressAssignment_consistent
    (state : OperationalState) (instId : InstId) (entry : ROBEntry) :
    state.findROBEntry instId = some entry →
    entry.addrAvailable →
    state.addressAssignment instId = entry.addr? := by
  intro h_find h_avail
  unfold addressAssignment
  simp [h_find, h_avail]

end GamI2e
