/-
COM: Alternative Axiomatic Model

This module re-exports all COM submodules. The COM (Communication) axiomatic model
is an alternative formulation of GAM that is more suitable for model checking tools.

The COM model uses:
- Coherence order (co): per-address total order of stores
- From-reads (fr): derived from rf and co
- Program order same location (poloc)

And has two axioms:
- SC-per-Location: Acyclicity of rf ∪ co ∪ fr ∪ poloc
- Causality: Acyclicity of rfe ∪ co ∪ fr ∪ ppo

## Submodule Organization

- **COM/Definitions.lean**: Basic definitions (COM_scPerLocation, COM_causality, extendedCommunication)
- **COM/ECO.lean**: Extended communication order lemmas (eco_total_per_address, eco_poloc)
- **COM/CausalityHelpers.lean**: Utility lemmas for causality proofs (com_contained_in_mo, etc.)
- **COM/Causality.lean**: Main causality infrastructure (causality_transgen_mem_to_mo)
- **COM/Equivalence.lean**: Main theorems (GAM_subset_COM, COM_subset_GAM, GAM_iff_COM)
-/

import GamI2e.COM.Definitions
import GamI2e.COM.ECO
import GamI2e.COM.CausalityHelpers
import GamI2e.COM.Causality
import GamI2e.COM.Equivalence
