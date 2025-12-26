# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## CRITICAL: The Paper is the Source of Truth

**The research paper in `paper/*.tex` is the authoritative source for all definitions, theorems, and proof strategies.** Do not invent proof approaches or modify definitions without first consulting the paper.

When working on this project:
1. **Definitions must match the paper exactly** - If the Lean code differs from the paper, the Lean code is wrong
2. **Proof strategies come from the paper** - Read the relevant appendix/section before attempting a proof
3. **When stuck, consult the paper first** - The answer is almost always there

## Session Startup Workflow

**Follow these steps at the start of EVERY session:**

### Step 1: Read PLAN.md
```
Read PLAN.md to understand current status, remaining sorries, and proof insights.
```

### Step 2: Identify the relevant paper section
Use the Paper Reference Index below to find the relevant section for the sorry you're working on:
- COM/GAM equivalence → `ComProofs.tex` (Appendix C)
- eco relation, SC-per-Location → `ComProofs.tex` Lemmas 3-4 and SC-per-Location theorem
- GAM axioms → `gam.tex` Section 4.1
- Operational semantics → `gam.tex` Section 4.2

### Step 3: Read the paper section
```
Read paper/ComProofs.tex  # or the relevant file
```
Extract the exact:
- **Definition** (e.g., "eco = co ∪ fr ∪ co*;rf ∪ rf⁻¹;co*;rf")
- **Theorem statement** (e.g., "For all pairs i₁, i₂ of memory accesses to the same address, either i₁ eco i₂ or i₂ eco i₁")
- **Proof strategy** (e.g., "By construction. All pairs of same-address writes are ordered in co...")

### Step 4: Verify Lean matches paper
Compare the Lean definitions/theorems against the paper. If they differ, fix the Lean code first.

### Step 5: Apply proof strategy from paper
Use the paper's proof strategy, not an invented one. The subagents can then fill in the tactical details.

### Step 6: Run subagents for tactical work
```
1. Get goal state: mcp__lean-lsp__lean_goal(file, line)
2. Try fast fill: Task(subagent_type="lean4-subagents:lean4-sorry-filler", ...)
3. If failed, escalate: Task(subagent_type="lean4-subagents:lean4-sorry-filler-deep", ...)
4. Verify: lake build
```

### Step 7: Update PLAN.md
Document progress, insights, and any remaining work.

## Common Mistakes to Avoid

1. **Inventing proof strategies** - The paper has the proof. Read it first.
2. **Modifying definitions to make proofs easier** - If a proof is hard, you're probably missing something from the paper.
3. **Using co+ when paper says co*** - Pay attention to reflexive-transitive (co*) vs transitive (co+) closures.
4. **Assuming eco is irreflexive** - With the paper's definition, eco is reflexive on loads. This is intentional.
5. **Trying to prove eco ⊆ mo** - The paper's SC-per-Location proof uses cycle reduction, not this approach.

## Lean 4 Gotchas

### Induction Variable Naming (the `✝` issue)

When using `induction h_path with` on a `TransGen` or similar inductive type, Lean renames the endpoint variables with a dagger (`✝`) suffix. For example:

```lean
-- If you have:
theorem foo (a b : Instruction) (h_path : TransGen r a b) : ... := by
  induction h_path with
  | single h_edge =>
    -- Here, the goal mentions `b✝`, NOT `b`!
    -- `b` is still in scope but refers to the ORIGINAL value
    -- `b✝` is the induction variable that changes
```

**Solutions:**
1. Use `rename_i` to give meaningful names: `rename_i endpoint`
2. Use underscores for variables you'll refer to via the induction: `theorem foo (a _ : Instruction)`
3. Check the goal state with `mcp__lean-lsp__lean_goal` before writing tactics
4. When the goal mentions `b✝`, use `_` in tactic arguments to let Lean infer it, e.g., `exact ⟨a, h_a_mem, Or.inl rfl, h_ppo⟩` instead of hardcoding `b`

The `tail` case is especially tricky because it introduces TWO new variables (the intermediate node and the new endpoint).

## Key Files to Know

| File | Purpose |
|------|---------|
| `PLAN.md` | Project status, remaining work, proof strategies |
| `CLAUDE.md` | This file - build instructions, paper index |
| `GamI2e/COM.lean` | Main file with remaining sorries (GAM↔COM equivalence) |
| `paper/*.tex` | **Source of truth** - all definitions and proofs |
| `paper/ComProofs.tex` | GAM/COM equivalence proofs (most relevant for current work) |

## Project Overview

This is a Lean 4 formalization project for weak memory consistency models, specifically:
- **GAM (General Atomic Memory model)**: A parameterized memory model for atomic memory systems
- **I2E (Instantaneous Instruction Execution)**: A simplified model that forbids load-store reordering

The project aims to provide both axiomatic and operational definitions of these memory models and prove their equivalence. This work is based on the research paper "Weak Memory Models with Matching Axiomatic and Operational Definitions" (see `paper/` directory).

## Building and Testing

### Build the project
```bash
lake build
```

### Build and run the executable
```bash
lake exe gam-i2e
```

### Clean build artifacts
```bash
lake clean
```

### Update dependencies
```bash
lake update
```

### Build in verbose mode (to see trace logs)
```bash
lake build -v
```

### Elaborate a specific Lean file
```bash
lake env lean path/to/file.lean
```

## Architecture

### Project Structure
- **GamI2e/Basic.lean**: Core definitions and basic constructs (currently contains minimal placeholder code)
- **GamI2e.lean**: Root module that imports all library modules
- **Main.lean**: Entry point for the executable

### Lean Toolchain
- Using Lean 4.25.1 (`leanprover/lean4:v4.25.1`)
- Package manager: Lake (Lean's build system)

### Library Organization
The project is organized as a Lean library (`GamI2e`) with an executable (`gam-i2e`). New modules should be:
1. Created under `GamI2e/` directory
2. Imported in `GamI2e.lean` to be included in the library build
3. Named with proper capitalization (e.g., `GamI2e/MyModule.lean`)

## Theoretical Context

The formalization is based on proving that axiomatic and operational definitions of memory models are equivalent. Key concepts:

- **Atomic memory models**: Memory models where stores become globally visible instantaneously (multicopy atomic)
- **Operational models**: Abstract machine semantics that directly produce legal program behaviors
- **Axiomatic models**: Constraint-based specifications on legal program behaviors
- **Soundness**: Operational model only produces behaviors allowed by axiomatic model
- **Completeness**: Operational model can produce all behaviors permitted by axiomatic model

The GAM framework is parameterized by instruction orderings and fence semantics, making it adaptable to various memory model variants.

## Development Notes

When adding formalizations, consider:
- GAM permits intra-thread load-store reorderings
- I2E is a restricted version that forbids load-store reordering, resulting in simpler definitions
- Both models should have matching axiomatic and operational definitions
- Proofs should be structured to show soundness and completeness

## Using Lean 4 Subagents

This project has access to specialized Lean 4 subagents that can help with proof development. These are highly effective for making progress on sorries and optimizing proofs.

### Available Subagents

| Subagent | Purpose | When to Use |
|----------|---------|-------------|
| `lean4-sorry-filler` | Fast local attempts to fill sorries | First pass on simple sorries, mathlib-style proofs |
| `lean4-sorry-filler-deep` | Strategic resolution of stubborn sorries | Complex proofs needing refactoring or multi-file changes |
| `lean4-proof-repair` | Compiler-guided iterative repair | Fixing broken proofs, adapting to definition changes |
| `lean4-proof-golfer` | Reduce proof size without changing semantics | After proofs compile, to achieve 30-40% size reduction |
| `lean4-axiom-eliminator` | Remove nonconstructive axioms | After checking axiom hygiene |

### Subagent Usage Tips

1. **Model selection**: Use `model: sonnet` for most tasks. Use `model: opus` for complex multi-file refactoring.

2. **sorry-filler vs sorry-filler-deep**:
   - Start with `sorry-filler` for quick wins (mathlib searches, simple tactics)
   - Escalate to `sorry-filler-deep` when the fast pass fails or signature changes are needed
   - `sorry-filler-deep` can add hypotheses to theorems, create helper lemmas, and refactor across files

3. **proof-golfer** is very effective:
   - Achieved 46% reduction on `eco_poloc` (637 → 343 lines)
   - Creates helper lemmas to eliminate repetition
   - Removes verbose comments and inlines redundant steps
   - Always run `lake build` after each optimization

4. **proof-repair** for definition changes:
   - When changing a definition (like `extendedCommunication`), use proof-repair to fix dependent proofs
   - It can handle signature changes and update call sites

5. **Prompt tips**:
   - Include the exact goal state from `lean_goal`
   - Mention available lemmas (use `lean_local_search` to find them)
   - Specify whether the project uses mathlib (this one doesn't)
   - Ask the agent to report errors rather than work around them

### Example Workflow

```
1. Identify a sorry with `/lean4-theorem-proving:analyze-sorries`
2. Get goal state: `mcp__lean-lsp__lean_goal(file, line)`
3. Try fast fill: Task(subagent_type="lean4-subagents:lean4-sorry-filler", ...)
4. If failed, escalate: Task(subagent_type="lean4-subagents:lean4-sorry-filler-deep", ...)
5. After success, golf: Task(subagent_type="lean4-subagents:lean4-proof-golfer", ...)
6. Verify: `lake build`
```

### Script Path Note

The subagent scripts are located at:
```
~/.claude/plugins/marketplaces/lean4-skills/plugins/lean4-theorem-proving/scripts/
```

If `$HOME` is unset (e.g., on NixOS), scripts may need explicit paths.

## Paper Reference Index

The `paper/` directory contains the LaTeX source for "Weak Memory Models with Matching Axiomatic and Operational Definitions". Use this index to find specific content without reading the entire paper.

### File Structure Overview

| File | Content |
|------|---------|
| `Main.tex` | Document root, defines structure and includes |
| `definitions.tex` | LaTeX macros for notation (relations, orderings, timestamps) |

### Main Content Files

#### `Introduction.tex` - Background and Motivation
- Section 1: Introduction to weak memory models
- Section 2 (`\label{sec:background}`): Memory model background
  - 2.1: Atomic vs. non-atomic memory (multicopy atomicity)
  - 2.2: Instruction reorderings and single-thread semantics
  - 2.3: Fences for writing multithreaded programs

#### `related_work.tex` - Related Work
- Section 3 (`\label{sec:related}`): Prior work on SC, TSO, POWER, ARM models

#### `gam.tex` - GAM Model (Core Definitions)
- **Section 4** (`\label{sec:GAM}`): General Atomic Memory Model
- **4.1** (`\label{sec:gam:axiom}`): Axiomatic Definition of GAM
  - **Definition of `ordered` function**: Table 1 (TSO), Table 2 (RMO) - parameterizes memory/fence ordering
  - **Input relations**: Program order (`<_po`), read-from (`rf`), memory order (`<_mo`)

- **4.1.1** (`\label{sec:ppo}`): Preserved Program Order (`<_ppo`)
  - **Definition 1** (`\label{def:ppo-mem-fence}`): Preserved memory/fence order `<_ppomf`
  - **Definitions 2-5**: Read Set (RS), Write Set (WS), Address Read Set (ARS), data-dependency, addr-dependency
  - **Definition 6** (`\label{def:ppo-dep}`): Preserved dependency order `<_ppod` (4 cases)
  - **Definition 7** (`\label{def:ppo-same-addr}`): Preserved same-address order `<_pposa` (3 cases)
  - **Definition 8** (`\label{def:ppo}`): Full preserved program order `<_ppo` (transitive closure)

- **4.1.2**: GAM Memory Axioms
  - **Axiom Inst-Order**: `I_1 <_ppo I_2 => I_1 <_mo I_2`
  - **Axiom Load-Value**: Load reads from max-mo visible store

- **4.2** (`\label{sec:operational}`): Operational Definition of GAM
  - ROB-based processor model with speculative execution
  - Ghost states: `doneTS`, `addrTS`, `sdataTS`, `from`
  - **Operational Rules**: Fetch, Execute-Reg-to-Reg, Execute-Branch, Execute-Fence, Execute-Load, Compute-Store-Data, Execute-Store, Compute-Mem-Addr

- **4.3** (`\label{sec:op<axiom}`): Soundness Proof (Operational ⊆ Axiomatic)
  - **Lemma 1** (`\label{lem:rob:inv}`): 7 invariants for operational execution

- **4.4** (`\label{sec:axiom<op}`): Completeness Proof (Axiomatic ⊆ Operational)
  - Simulation algorithm with 8 invariants

#### `Axiomatic.tex` - COM Alternative Axioms
- **Section 5** (`\label{sec:COM}`): Alternative axiomatic formulation
  - Basic relations: `<_po`, `rf`, coherence `<_co`
  - Derived relations: `rfe` (external rf), `fr` (from-reads), `po_loc`
  - **Axiom SC-per-Location**: `acyclic(rf ∪ co ∪ fr ∪ po_loc)`
  - **Axiom Causality**: `acyclic(rfe ∪ co ∪ fr ∪ <_ppo)`
- **5.2**: Equivalence of GAM and COM (Lemmas 2-4)
- **5.3**: COM ⊆ GAM proof
- **5.4**: Empirical validation with Alloy model checker

#### `Instances.tex` - Comparing with Existing Models
- **Section 6** (`\label{sec:instance}`): GAM instances for existing models
  - 6.1: SC - Table 3 shows `ordered_SC`
  - 6.2: TSO - Table 1 shows `ordered_TSO`
  - 6.3: SPARC RMO (`\label{sec:compare-rmo}`) - Table 2, same-address load-load discussion
  - 6.4: WMM - Table 4 shows `ordered_WMM` (Commit/Reconcile fences)
  - 6.5: ARM v8.2 (`\label{sec:compare-arm}`) - RSW behavior, fri-rfi example
  - 6.6: Alpha - more relaxed dependency ordering
  - 6.7: RISC-V - Table 5 shows expected `ordered_RISC-V`

#### `i2e.tex` - GAM-I2E Model
- **Section 7** (`\label{sec:I2E}`, `\label{sec:i2e}`): Instantaneous Instruction Execution
- Key constraint: `ordered(Ld, St) = true` (forbids load-store reordering)
- **7.1**: GAM-I2E Axiomatic Model (same as GAM with LS ordering)
- **7.2**: GAM-I2E Operational Model
  - Simpler: processors execute in-order, local buffers for stores/fences
  - Memory system is a list `<_mo-i2e`
  - **Rules**: Execute-Reg-Branch, Execute-Store-Fence, Execute-Load, Dequeue-Store, Dequeue-Fence
- **7.3**: Soundness proof (I2E Operational ⊆ I2E Axiomatic)
- **7.4**: Completeness proof (I2E Axiomatic ⊆ I2E Operational)

#### `Conclusion.tex` - Summary
- **Section 8** (`\label{sec:conclusion}`): Brief conclusions

### Appendix Files (Detailed Proofs)

#### `gam_axi_contain_op.tex` - GAM Soundness Proof Details
- **Appendix A** (`\label{sec:gam_axi_contain_op}`): Full proof of Operational ⊆ Axiomatic
- Lemma on `<_ntppo-rob` changes under different rules
- Inductive proof of all 7 invariants for each operational rule type

#### `gam_op_contain_axi.tex` - GAM Completeness Proof Details
- **Appendix B** (`\label{sec:gam_op_contain_axi}`): Full proof of Axiomatic ⊆ Operational
- Simulation algorithm details
- Proof that guards are satisfied and no kills occur

#### `ComProofs.tex` - GAM/COM Equivalence Proofs
- **Appendix C** (`\label{sec:gamcom}`): GAM ⊆ COM detailed proofs
- Lemmas on `<_eco` relation
- **Appendix D** (`\label{sec:alloy}`): Alloy model code for empirical validation

#### `i2e_op_contain_axi.tex` - I2E Completeness Proof Details
- **Appendix E** (`\label{sec:i2_op_contain_axi}`): Full proof of I2E Axiomatic ⊆ I2E Operational
- Simulation algorithm with 6 invariants

### Key Definitions Quick Reference

| Concept | Definition Location | Description |
|---------|---------------------|-------------|
| `ordered(I_old, I_new)` | `gam.tex` §4, Tables 1-5 | Memory/fence ordering function |
| `<_ppo` | `gam.tex` Def 8 | Preserved program order |
| `<_ppomf` | `gam.tex` Def 1 | Preserved memory/fence order |
| `<_ppod` | `gam.tex` Def 6 | Preserved dependency order |
| `<_pposa` | `gam.tex` Def 7 | Preserved same-address order |
| `<_po` | `gam.tex` §4.1 | Program order (per-processor total order) |
| `<_mo` | `gam.tex` §4.1 | Memory order (global total order) |
| `rf` | `gam.tex` §4.1 | Read-from relation |
| `<_co` | `Axiomatic.tex` §5.1 | Coherence order (per-address store order) |
| `fr` | `Axiomatic.tex` §5.1 | From-reads = rf⁻¹;co |
| ROB ghost states | `gam.tex` §4.3 | doneTS, addrTS, sdataTS, from |
| I2E buffer | `i2e.tex` §7.2 | Local store/fence buffer |

### Notation Reference (from `definitions.tex`)

| LaTeX Macro | Rendered | Meaning |
|-------------|----------|---------|
| `\ProgOrd` | `<_po` | Program order |
| `\MemOrd` | `<_mo` | Memory order |
| `\PreservePO` | `<_ppo` | Preserved program order |
| `\LSFOrd` | `<_ppomf` | Preserved memory/fence order |
| `\DepOrd` | `<_ppod` | Preserved dependency order |
| `\SameAddrOrd` | `<_pposa` | Preserved same-address order |
| `\ReadFrom` | `→_rf` | Read-from |
| `\Coh` | `<_co` | Coherence |
| `\Fr` | `→_fr` | From-reads |
| `\DataDep` | `<_ddep` | Data dependency |
| `\AddrDep` | `<_adep` | Address dependency |
| `\IIEMemOrd` | `<_mo-i2e` | I2E memory order |
| `\IIEPreservePO` | `<_ppo-i2e` | I2E preserved program order |
