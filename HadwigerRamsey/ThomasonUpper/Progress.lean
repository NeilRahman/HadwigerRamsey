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

/-!
Checked ingredients toward Theorem 1.5 of the October 31 manuscript.

`HadwigerRamsey.ThomasonUpper.Statement` records the target proposition.
No proof of that proposition is supplied here. The complete-equipartition
construction, existence of the reservoirs, and uniform asymptotic assembly
remain to be formalized. Vertex-deletion density stability and the finite
rounding, trimming, and regularization ingredients are proved.
-/
