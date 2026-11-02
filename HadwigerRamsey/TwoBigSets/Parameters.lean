import Mathlib

open Finset Real
namespace HadwigerRamsey.TwoBigSets

theorem small_parameter (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/20 ∧ r ≤ 2*ε/3 ∧
      1-ε < (1-r)*(1-2*r) := by
  refine ⟨min (ε/8) (1/20),by positivity,min_le_right _ _,?_,?_⟩
  · have hh := min_le_left (ε/8) (1/20)
    linarith
  · have hh := min_le_left (ε/8) (1/20)
    nlinarith only [hh,hε,sq_nonneg (min (ε/8) (1/20))]

theorem two_good_or_two_bad (P : Fin 3 → Prop) :
    (∃ i j : Fin 3, i ≠ j ∧ P i ∧ P j) ∨
    (∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ¬P i ∧ ¬P j) := by
  classical
  by_cases h0 : P 0
  · by_cases h1 : P 1
    · exact Or.inl ⟨0,1,by decide,h0,h1⟩
    · by_cases h2 : P 2
      · exact Or.inl ⟨0,2,by decide,h0,h2⟩
      · exact Or.inr ⟨1,2,0,by decide,by decide,by decide,h1,h2⟩
  · by_cases h1 : P 1
    · by_cases h2 : P 2
      · exact Or.inl ⟨1,2,by decide,h1,h2⟩
      · exact Or.inr ⟨0,2,1,by decide,by decide,by decide,h0,h2⟩
    · exact Or.inr ⟨0,1,2,by decide,by decide,by decide,h0,h1⟩

theorem final_comparison {n a : ℕ} {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    (ha : 2 ≤ a) (han : a ≤ n) (hsize : r^3/2*n ≤ (a : ℝ)) :
    C*n/sqrt (log (n : ℝ)) ≤
      (2*C/r^3)*a/sqrt (log (a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hroot : 0 < sqrt (log (a : ℝ)) :=
    sqrt_pos.mpr (log_pos (by exact_mod_cast (by omega : 1 < a)))
  have hrootle : sqrt (log (a : ℝ)) ≤ sqrt (log (n : ℝ)) :=
    sqrt_le_sqrt (log_le_log haR (by exact_mod_cast han))
  have hcoef : C*n ≤ (2*C/r^3)*a := by
    have hh := mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ 2*C/r^3 by positivity)
    have he : (2*C/r^3)*(r^3/2*n) = C*n := by field_simp [hr.ne']
    simpa only [he] using hh
  calc
    _ ≤ (2*C/r^3)*a/sqrt (log (n : ℝ)) :=
      div_le_div_of_nonneg_right hcoef (sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hroot hrootle

end HadwigerRamsey.TwoBigSets
