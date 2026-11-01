import HadwigerRamsey.ThomasonUpper.Density

open scoped BigOperators Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.BipMinor

/-- Just one off-diagonal summand already gives enough entropy. -/
theorem entropy_lower {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    {epsilon : ℝ} (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hmass : ∀ i, 1/4 ≤ classMass c i) (hcross : 1-epsilon ≤ blockDensity G c 0 1) :
    (-log epsilon)/16 ≤ cappedLambda G c epsilon := by
  have hl : 0 ≤ -log epsilon := by linarith [log_nonpos he.le he1]
  have hcap : cappedDensity G c epsilon 0 1 = 1-epsilon := min_eq_right hcross
  have ht : ∀ i j, 0 ≤ classMass c i*classMass c j*(-log (1-cappedDensity G c epsilon i j)) := by
    intro i j
    exact mul_nonneg (mul_nonneg (classMass_nonneg _ _) (classMass_nonneg _ _))
      (log_weight_bounds he (cappedDensity_bounds G c he1 i j).1 (cappedDensity_bounds G c he1 i j).2).1
  have hprod : (1/16:ℝ) ≤ classMass c 0*classMass c 1 := by nlinarith only [hmass 0,hmass 1]
  calc
    _ ≤ classMass c 0*classMass c 1*(-log epsilon) := by nlinarith only [mul_le_mul_of_nonneg_right hprod hl]
    _ = classMass c 0*classMass c 1*(-log (1-cappedDensity G c epsilon 0 1)) := by rw [hcap]; congr 3; ring
    _ ≤ ∑ j : Fin 2, classMass c 0*classMass c j*(-log (1-cappedDensity G c epsilon 0 j)) :=
      single_le_sum (fun j _ => ht 0 j) (mem_univ 1)
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, classMass c i*classMass c j*(-log (1-cappedDensity G c epsilon i j)) :=
      single_le_sum (fun i _ => sum_nonneg (fun j _ => ht i j)) (mem_univ 0)
end HadwigerRamsey.BipMinor
