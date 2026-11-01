import HadwigerRamsey.ThomasonUpper.DensityLower
import HadwigerRamsey.ThomasonUpper.Domination
import HadwigerRamsey.ThomasonUpper.ReservoirDomination
import HadwigerRamsey.ThomasonUpper.BranchSets
import HadwigerRamsey.ThomasonUpper.Deletion
import HadwigerRamsey.ThomasonUpper.Stability
import HadwigerRamsey.ThomasonUpper.Menger
import HadwigerRamsey.ThomasonUpper.PathAllocation
import HadwigerRamsey.ThomasonUpper.DensityDeletion
import HadwigerRamsey.ThomasonUpper.Trimming
import HadwigerRamsey.ThomasonUpper.Regularization
import HadwigerRamsey.ThomasonUpper.FiniteAssembly
import HadwigerRamsey.ThomasonUpper.AllocationBudgets
import HadwigerRamsey.ThomasonUpper.Capping
import HadwigerRamsey.ThomasonUpper.NonneighborSampling
import HadwigerRamsey.ThomasonUpper.SelectedBlocks

import HadwigerRamsey.ThomasonUpper.MultitypeFinite
import HadwigerRamsey.ThomasonUpper.MultitypeAsymptotic
import HadwigerRamsey.ThomasonUpper.AsymptoticParameters

/-!
Checked appendix ingredients used in the completed proof of Theorem 1.5.

The public endpoint `HadwigerRamsey.thomasonupper` is in
`HadwigerRamsey/ThomasonUpper.lean`; `Final.lean` assembles the proof.
A.1 has its full complete-equipartition conclusion. The uniform
complete-family consequence of A.3 is in `AsymptoticFamily.lean`.
The reservoirs, allocation budgets, capped spanning subgraph, and
finite clique-minor construction imported here supply the final assembly.
-/
