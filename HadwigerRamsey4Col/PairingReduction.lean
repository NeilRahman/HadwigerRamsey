import HadwigerRamsey4Col.ReindexProgram
import HadwigerRamsey4Col.AttainingConstruction
import HadwigerRamsey4Col.Lemma5

open Real Finset
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
namespace HadwigerRamsey4Col

def pairingColour : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,0,1,2],![0,0,2,1],![1,2,0,0],![2,1,0,0]]

lemma pairingColour_symm (i j : Fin 4) : pairingColour i j=pairingColour j i := by
  fin_cases i <;> fin_cases j <;> rfl
lemma pairingColour_ne_three (i j : Fin 4) : pairingColour i j≠3 := by
  fin_cases i <;> fin_cases j <;> decide

lemma unique_pairing : ∀ c i j : Fin 4, i≠j → c≠3 → c≠pairingColour i j →
    optimalLabel c i≠optimalLabel c j := by decide

lemma pairing_labels : ∀ i j k : Fin 4, i≠j →
    (optimalLabel (pairingColour i j) k=optimalLabel (pairingColour i j) i ↔ k=i ∨ k=j) := by decide

namespace FiniteProgram
variable {β : Type} [Fintype β] [DecidableEq β]
variable (P : FiniteProgram (Fin 4) β)
variable (hpattern : ∀ c i j, P.label c i=P.label c j ↔ optimalLabel c i=optimalLabel c j)

include hpattern

lemma canonical_density_zero (c i j : Fin 4) (h : optimalLabel c i≠optimalLabel c j) :
    P.density c i j=0 := P.density_zero c i j (fun he => h ((hpattern c i j).mp he))

lemma canonical_pair_sum (i j : Fin 4) (hij : i≠j) :
    P.density 3 i j+P.density (pairingColour i j) i j=1 := by
  have hz (c : Fin 4) (hc : c≠3 ∧ c≠pairingColour i j) : P.density c i j=0 := by
    apply P.canonical_density_zero hpattern
    exact unique_pairing c i j hij hc.1 hc.2
  calc
    _ = ∑ c ∈ ({3,pairingColour i j} : Finset (Fin 4)), P.density c i j := by
      simp [Ne.symm (pairingColour_ne_three i j)]
    _ = ∑ c,P.density c i j := by
      apply sum_subset (subset_univ _)
      intro c _ hc
      apply hz
      simpa [mem_insert,mem_singleton,not_or] using hc
    _ = 1 := P.density_sum i j

omit hpattern in
lemma canonical_diag_sum (i : Fin 4) :
    P.density 3 i i+(∑ j ∈ univ.erase i,P.density (pairingColour i j) i i)=1 := by
  have hs := P.density_sum i i
  rw [sum_erase_eq_sub (mem_univ i)]
  simp only [Fin.sum_univ_four] at hs ⊢
  fin_cases i
  · change P.density 3 0 0+(P.density 0 0 0+P.density 0 0 0+P.density 1 0 0+P.density 2 0 0-P.density 0 0 0)=1
    linarith!
  · change P.density 3 1 1+(P.density 0 1 1+P.density 0 1 1+P.density 2 1 1+P.density 1 1 1-P.density 0 1 1)=1
    linarith!
  · change P.density 3 2 2+(P.density 1 2 2+P.density 2 2 2+P.density 0 2 2+P.density 0 2 2-P.density 0 2 2)=1
    linarith!
  · change P.density 3 3 3+(P.density 2 3 3+P.density 1 3 3+P.density 0 3 3+P.density 0 3 3-P.density 0 3 3)=1
    linarith!

noncomputable def asPairing : PairingData where
  mass := P.mass
  mass_nonneg := P.mass_nonneg
  mass_sum := P.mass_sum
  span := P.density 3
  span_symm := P.density_symm 3
  span_nonneg := P.density_nonneg 3
  span_lt_one := P.density_lt_one 3
  pair := fun i j => P.density (pairingColour i j) i j
  pair_symm := by intro i j; rw [pairingColour_symm,P.density_symm]
  pair_nonneg := fun i j _ => P.density_nonneg _ i j
  pair_lt_one := fun i j _ => P.density_lt_one _ i j
  offdiag_sum := P.canonical_pair_sum hpattern
  diag := fun i j => P.density (pairingColour i j) i i
  diag_nonneg := fun i j _ => P.density_nonneg _ i i
  diag_lt_one := fun i j _ => P.density_lt_one _ i i
  diag_sum := P.canonical_diag_sum

lemma canonical_part_pair (i j : Fin 4) (hij : i≠j) :
    P.part (pairingColour i j) (P.label (pairingColour i j) i)={i,j} := by
  ext k
  simp only [part,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
  rw [hpattern]
  exact pairing_labels i j k hij

lemma asPairing_span_le : (P.asPairing hpattern).spanEnergy ≤ P.bound := by
  have he : P.part 3 (P.label 3 0)=univ := by
    ext i
    simp only [part,mem_filter,mem_univ,true_and,iff_true]
    exact (hpattern 3 i 0).mpr (by fin_cases i <;> rfl)
  have hh := P.entropy_le 3 (P.label 3 0)
  change regionCost P.mass (P.density 3) (P.part 3 (P.label 3 0)) (P.part 3 (P.label 3 0)) ≤ P.bound at hh
  rw [he] at hh
  exact hh

lemma asPairing_pair_le (i j : Fin 4) (hij : i≠j) :
    (P.asPairing hpattern).pairEnergy i j ≤ P.bound := by
  have hh := P.entropy_le (pairingColour i j) (P.label (pairingColour i j) i)
  change regionCost P.mass (P.density (pairingColour i j))
    (P.part (pairingColour i j) (P.label (pairingColour i j) i))
    (P.part (pairingColour i j) (P.label (pairingColour i j) i)) ≤ _ at hh
  rw [P.canonical_part_pair hpattern i j hij] at hh
  have he : regionCost P.mass (P.density (pairingColour i j)) {i,j} {i,j} =
      (P.asPairing hpattern).pairEnergy i j := by
    simp only [regionCost,Finset.sum_pair hij,PairingData.pairEnergy,asPairing]
    rw [pairingColour_symm j i,P.density_symm (pairingColour i j) j i]
    ring
  rwa [he] at hh

lemma canonical_lower_bound : tStar parameter ≤ P.bound :=
  lemma5_pairing_lower_bound (P.asPairing hpattern) P.bound (P.asPairing_span_le hpattern)
    (P.asPairing_pair_le hpattern)

end FiniteProgram
end HadwigerRamsey4Col
