import HadwigerRamsey.Weights

open scoped BigOperators
open Finset Real
namespace HadwigerRamsey

/-- The relative size of a partition class. A partition is encoded by its class map. -/
noncomputable def classMass {n k : ℕ} (τ : Fin n → Fin k) (i : Fin k) : ℝ :=
  (univ.filter (fun u => τ u = i)).card / (n : ℝ)

noncomputable def blockLambda {n k : ℕ} (τ : Fin n → Fin k)
    (p : Fin k → Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, classMass τ i * classMass τ j * (-log (1-p i j))

lemma sum_pullback {n k : ℕ} (τ : Fin n → Fin k) (a : Fin k → ℝ) :
    ∑ u, a (τ u) = ∑ i, ((univ.filter (fun u => τ u = i)).card : ℝ) * a i := by
  classical
  rw [← Finset.sum_fiberwise univ τ (fun u => a (τ u))]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ _u ∈ univ.filter (fun u => τ u = i), a i := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [(mem_filter.mp hu).2]
    _ = _ := by simp

/-- The manuscript's block-weighted average equals the vertex-pair average. -/
lemma blockLambda_identity {n k : ℕ} (hn : 0 < n) (τ : Fin n → Fin k)
    (p : Fin k → Fin k → ℝ) :
    (n : ℝ)^2 * blockLambda τ p = ∑ u, ∑ v, -log (1-p (τ u) (τ v)) := by
  classical
  rw [sum_pullback τ (fun i => ∑ v, -log (1-p i (τ v)))]
  conv_rhs =>
    arg 2
    ext i
    rw [sum_pullback τ (fun j => -log (1-p i j))]
  dsimp [blockLambda, classMass]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp

/-- Bounds on logarithmic edge weights under the theorem's probability assumptions. -/
lemma log_weight_bounds {ε q : ℝ} (hε : 0 < ε) (hq : 0 ≤ q) (hqe : q ≤ 1-ε) :
    0 ≤ -log (1-q) ∧ -log (1-q) ≤ -log ε := by
  have hpos : 0 < 1-q := by linarith
  constructor
  · have := Real.log_nonpos (by linarith : 0 ≤ 1-q) (by linarith : 1-q ≤ 1)
    linarith
  · exact neg_le_neg (Real.log_le_log hε (by linarith))

end HadwigerRamsey
