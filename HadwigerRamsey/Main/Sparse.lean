import HadwigerRamsey.ThomasonUpper.Density

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.Main

theorem internal_density_weighted {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    (S.card : ℝ)^2 * internalDensity G S ≤
      (G.interedges S S).card + (S.card : ℝ) := by
  classical
  by_cases hs : 2 ≤ S.card
  · have hden : (0 : ℝ) < S.card.choose 2 := by exact_mod_cast Nat.choose_pos hs
    have he : internalDensity G S * (S.card.choose 2 : ℝ) =
        ((G.induce (S : Set (Fin n))).edgeFinset.card : ℝ) := by
      unfold internalDensity
      exact div_mul_cancel₀ _ hden.ne'
    rw [Nat.cast_choose_two] at he
    have hc := card_internal_interedges G S
    have hcR : ((G.interedges S S).card : ℝ) =
        2*((G.induce (S : Set (Fin n))).edgeFinset.card : ℝ) := by exact_mod_cast hc
    have hp := internalDensity_le_one G S
    have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg S.card)
    nlinarith only [he,hcR,hh]
  · have hc : S.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [internalDensity,hc,Nat.cast_zero,div_zero,mul_zero]
    positivity

theorem weighted_density_upper {n k : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (τ : Fin n → Fin k) :
    (∑ i, ∑ j, classMass τ i*classMass τ j*blockDensity G τ i j) ≤
      2*(G.edgeFinset.card : ℝ)/(n : ℝ)^2 + 1/(n : ℝ) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm : ∀ i j,
      classMass τ i*classMass τ j*blockDensity G τ i j ≤
        ((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ)/(n : ℝ)^2 +
          if i=j then classMass τ i/n else 0 := by
    intro i j
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,blockDensity,if_pos rfl]
      have hh := div_le_div_of_nonneg_right
        (internal_density_weighted G (classVertices τ i)) (sq_nonneg (n : ℝ))
      have hL : classMass τ i*classMass τ i*internalDensity G (classVertices τ i) =
          ((classVertices τ i).card : ℝ)^2*internalDensity G (classVertices τ i)/(n : ℝ)^2 := by
        change (((classVertices τ i).card : ℝ)/n)*(((classVertices τ i).card : ℝ)/n)*_ = _
        ring
      have hR : ((G.interedges (classVertices τ i) (classVertices τ i)).card : ℝ)/(n : ℝ)^2 +
          classMass τ i/n =
          (((G.interedges (classVertices τ i) (classVertices τ i)).card : ℝ) +
            (classVertices τ i).card)/(n : ℝ)^2 := by
        change _ + (((classVertices τ i).card : ℝ)/n)/n = _
        ring
      rw [hL,hR]
      exact hh
    · rw [if_neg hij,blockDensity,if_neg hij,add_zero]
      by_cases hi : (classVertices τ i).card = 0
      · have hm : classMass τ i=0 := by change ((classVertices τ i).card : ℝ)/n=0; simp [hi]
        rw [hm,zero_mul,zero_mul]
        positivity
      by_cases hj : (classVertices τ j).card = 0
      · have hm : classMass τ j=0 := by change ((classVertices τ j).card : ℝ)/n=0; simp [hj]
        rw [hm,mul_zero,zero_mul]
        positivity
      have hiR : ((classVertices τ i).card : ℝ) ≠ 0 := by exact_mod_cast hi
      have hjR : ((classVertices τ j).card : ℝ) ≠ 0 := by exact_mod_cast hj
      apply le_of_eq
      simp only [SimpleGraph.edgeDensity_def,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]
      change ((classVertices τ i).card : ℝ)/n * (((classVertices τ j).card : ℝ)/n) *
        (((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ)/
          (((classVertices τ i).card : ℝ)*(classVertices τ j).card)) = _
      field_simp
  calc
    _ ≤ ∑ i, ∑ j, (((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ)/(n : ℝ)^2 +
        if i=j then classMass τ i/n else 0) := sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
    _ = _ := by
      have hcount : (∑ i, ∑ j,
          ((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ)) =
          2*(G.edgeFinset.card : ℝ) := by exact_mod_cast sum_card_block_interedges G τ
      simp only [sum_add_distrib,sum_ite_eq,mem_univ,if_true]
      simp_rw [←sum_div]
      rw [hcount,sum_classMass hn]

theorem active_weighted_density_upper {n m : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (τ : Fin n → Fin (m+1)) :
    (∑ i : Fin m, ∑ j : Fin m,
      classMass τ i.castSucc*classMass τ j.castSucc*blockDensity G τ i.castSucc j.castSucc) ≤
      2*(G.edgeFinset.card : ℝ)/(n : ℝ)^2 + 1/(n : ℝ) := by
  have hnon : ∀ i j, 0 ≤ classMass τ i*classMass τ j*blockDensity G τ i j := by
    intro i j
    exact mul_nonneg (mul_nonneg (classMass_nonneg _ _) (classMass_nonneg _ _))
      (blockDensity_nonneg _ _ _ _)
  apply le_trans ?_ (weighted_density_upper hn G τ)
  rw [Fin.sum_univ_castSucc]
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin (m+1),
        classMass τ i.castSucc*classMass τ j*blockDensity G τ i.castSucc j := by
      apply sum_le_sum
      intro i _
      rw [Fin.sum_univ_castSucc]
      exact le_add_of_nonneg_right (hnon _ _)
    _ ≤ _ := le_add_of_nonneg_right (sum_nonneg fun j _ => hnon _ _)

end HadwigerRamsey.Main
