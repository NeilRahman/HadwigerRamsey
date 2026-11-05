import HadwigerRamsey4Col.ProgramPatterns
import HadwigerRamsey4Col.LargeAtom
import HadwigerRamsey4Col.Lemma4
import HadwigerRamsey4Col.Lemma5
import HadwigerRamsey4Col.Lemma6
import HadwigerRamsey4Col.Theorem1
import HadwigerRamsey4Col.Ramsey

/-! The four-colour Hadwiger--Ramsey asymptotic with its exact leading constant.
The component optimization proves Theorem 1 and numbered results 2–6 of the local
analytic manuscript; the Ramsey limit follows from `ComponentTransfer.theorem5`. -/

#print axioms HadwigerRamsey4Col.beta4_eq_of_root
#print axioms HadwigerRamsey4Col.theorem1_1
#print axioms HadwigerRamsey4Col.theorem1_1_explicit

#print axioms HadwigerRamsey4Col.lemma2
#print axioms HadwigerRamsey4Col.component_pattern_classification
#print axioms HadwigerRamsey4Col.exists_unique_parameter
#print axioms HadwigerRamsey4Col.tStar_lt_threshold
#print axioms HadwigerRamsey4Col.PairingData.large_atom_of_threshold
#print axioms HadwigerRamsey4Col.lemma3
#print axioms HadwigerRamsey4Col.lemma3_at_optimum
#print axioms HadwigerRamsey4Col.entropy_hasDerivAt
#print axioms HadwigerRamsey4Col.entropy_quadratic_lower
#print axioms HadwigerRamsey4Col.lemma4
#print axioms HadwigerRamsey4Col.dualValue_eq_unordered
#print axioms HadwigerRamsey4Col.lemma5
#print axioms HadwigerRamsey4Col.PairingData.dual_bound
#print axioms HadwigerRamsey4Col.lemma5_pairing_lower_bound
#print axioms HadwigerRamsey4Col.first_normalized_capacity
#print axioms HadwigerRamsey4Col.second_normalized_capacity
#print axioms HadwigerRamsey4Col.lemma6

#print axioms HadwigerRamsey4Col.FiniteProgram.merge
#print axioms HadwigerRamsey4Col.FiniteProgram.no_ball
#print axioms HadwigerRamsey4Col.FiniteProgram.lower_bound
#print axioms HadwigerRamsey4Col.attaining_objective
#print axioms HadwigerRamsey4Col.instance_lower_bound
#print axioms HadwigerRamsey4Col.beta4_eq
#print axioms HadwigerRamsey4Col.theorem1
