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
Checked ingredients toward Theorem 1.5 of the October 31 manuscript.

`HadwigerRamsey.ThomasonUpper.Statement` records the target proposition.
No proof of that proposition is supplied here. Appendix A.1's complete
multitype equipartition theorem is proved, with a nonempty class-index set.
The uniform asymptotic corollary A.3 and final uniform assembly remain.
The reservoirs, allocation budgets, capped spanning subgraph, and finite
clique-minor assembly are proved. The exact log formula for A.1's P and
a uniform probability estimate under a quadratic entropy margin are proved;
a many-parts consequence for exact-multiple classes now explicitly uses A.1.
The constants gamma, xi, tau, phi, omega have been chosen uniformly.
The required margin still needs to be obtained from the rounded and trimmed
graph parameters in A.3, followed by its final part-count comparisons.
-/
