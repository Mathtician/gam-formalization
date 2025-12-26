/-
COM: Extended Communication Order (ECO) Lemmas

This module re-exports all ECO submodules. The ECO module contains lemmas about
the extended communication order (eco) relation and proves key properties like
eco_total_per_address, eco_poloc, and sc_per_location_acyclic.

## Submodule Organization

- **ECO/Base.lean**: Basic ECO lemmas (eco_total_per_address, eco_poloc)
- **ECO/SCRel.lean**: SC-per-Location relation definition and edge type analysis
- **ECO/SCRelPath.lean**: Path utilities (SCRelLen, path decomposition, load/store path analysis)
- **ECO/SCPerLocation.lean**: Main SC-per-Location acyclicity proof
-/

import GamI2e.COM.ECO.Base
import GamI2e.COM.ECO.SCRel
import GamI2e.COM.ECO.SCRelPath
import GamI2e.COM.ECO.SCPerLocation
