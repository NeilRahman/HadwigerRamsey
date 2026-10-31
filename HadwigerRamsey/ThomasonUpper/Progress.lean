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
import HadwigerRamsey.ThomasonUpper.NonneighborWeights

/-!
Checked ingredients toward Theorem 1.5 of the October 31 manuscript.

`HadwigerRamsey.ThomasonUpper.Statement` records the target proposition.
No proof of that proposition is supplied here. The complete-equipartition
construction, the rest of its uniform asymptotic corollary, and the final
uniform assembly remain to be formalized. The reservoirs, allocation budgets,
capped spanning subgraph, and finite clique-minor assembly are proved.
-/
