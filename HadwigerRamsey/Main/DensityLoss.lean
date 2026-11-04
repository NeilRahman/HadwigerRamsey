import HadwigerRamsey.ThomasonUpper.DensityDeletion

open scoped Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.Main

theorem internalDensity_inter_loss {n : ℕ} (G : SimpleGraph (Fin n))
    (S P : Finset (Fin n)) {lam e : ℝ} (hlam : 0 < lam) (he : 0 ≤ e)
    (hS : 2 ≤ S.card) (hsize : lam*n ≤ (S.card : ℝ))
    (hP : (1-e)*n ≤ (P.card : ℝ)) :
    internalDensity G S - 8*e/lam ≤ internalDensity G (S ∩ P) := by
  classical
  let Z : Finset (Fin n) := univ \ P
  have hZn : (Z.card : ℝ) ≤ e*n := by
    dsimp [Z]
    rw [card_sdiff_of_subset (subset_univ P),card_univ,Fintype.card_fin,
      Nat.cast_sub (by simpa using P.card_le_univ : P.card ≤ n)]
    linarith
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have hden : (Z.card : ℝ)/S.card ≤ e/lam := by
    apply (div_le_div_iff₀ hSc hlam).mpr
    have hh := mul_le_mul_of_nonneg_left hZn hlam.le
    have hh' := mul_le_mul_of_nonneg_left hsize he
    nlinarith only [hh,hh']
  have hh := internalDensity_deletion_bound G S Z hS
  have hsd : S \ Z = S ∩ P := by ext v; simp [Z]
  rw [hsd] at hh
  have hl := (abs_le.mp hh).1
  have h8 : 8*(Z.card : ℝ)/S.card ≤ 8*e/lam := by
    have hm := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 8)
    simpa only [mul_div_assoc] using hm
  linarith only [hl,h8]

theorem edgeDensity_inter_loss {n : ℕ} (G : SimpleGraph (Fin n))
    (S T P : Finset (Fin n)) {lam e : ℝ} (hlam : 0 < lam) (he : 0 ≤ e)
    (hS : lam*n ≤ (S.card : ℝ)) (hT : lam*n ≤ (T.card : ℝ))
    (hP : (1-e)*n ≤ (P.card : ℝ)) :
    (G.edgeDensity S T : ℝ) - 2*e/lam ≤ G.edgeDensity (S ∩ P) (T ∩ P) := by
  classical
  let Z : Finset (Fin n) := univ \ P
  have hZn : (Z.card : ℝ) ≤ e*n := by
    dsimp [Z]
    rw [card_sdiff_of_subset (subset_univ P),card_univ,Fintype.card_fin,
      Nat.cast_sub (by simpa using P.card_le_univ : P.card ≤ n)]
    linarith
  have hh := edgeDensity_deletion_bound G S T Z hlam he hS hT hZn
  have hsd : ∀ U : Finset (Fin n), U \ Z = U ∩ P := by
    intro U
    ext v
    simp [Z]
  rw [hsd,hsd] at hh
  linarith [(abs_le.mp hh).1]

end HadwigerRamsey.Main
