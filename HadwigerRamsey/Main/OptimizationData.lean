import HadwigerRamsey.Main.Analytic

open scoped BigOperators Classical
open Finset Real
namespace HadwigerRamsey.Main

noncomputable def fillMatrix {m : ℕ} (q : Fin m → Fin m → ℝ) :
    Fin (m+1) → Fin (m+1) → ℝ :=
  Fin.lastCases (fun _ => 1/2) (fun i => Fin.lastCases (1/2) (q i))

@[simp] theorem fillMatrix_active {m : ℕ} (q : Fin m → Fin m → ℝ) (i j : Fin m) :
    fillMatrix q i.castSucc j.castSucc = q i j := by simp [fillMatrix]

@[simp] theorem fillMatrix_last_left {m : ℕ} (q : Fin m → Fin m → ℝ) (j : Fin (m+1)) :
    fillMatrix q (Fin.last m) j = 1/2 := by simp [fillMatrix]

@[simp] theorem fillMatrix_last_right {m : ℕ} (q : Fin m → Fin m → ℝ) (i : Fin (m+1)) :
    fillMatrix q i (Fin.last m) = 1/2 := by
  cases i using Fin.lastCases <;> simp [fillMatrix]

theorem fillMatrix_symm {m : ℕ} (q : Fin m → Fin m → ℝ)
    (hq : ∀ i j, q i j = q j i) : ∀ i j, fillMatrix q i j = fillMatrix q j i := by
  intro i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp [hq]

theorem fillMatrix_energy {m : ℕ} (α : Fin (m+1) → ℝ)
    (hα : ∑ i, α i = 1) (q : Fin m → Fin m → ℝ) :
    Optimization.energy α (fillMatrix q) =
      Optimization.energy (fun i => α i.castSucc) q +
        (2*α (Fin.last m)-(α (Fin.last m))^2)*log 2 := by
  have hs : (∑ i : Fin m, α i.castSucc) + α (Fin.last m) = 1 := by
    simpa only [Fin.sum_univ_castSucc] using hα
  have hc : Optimization.logCost (1/2) = log 2 := by
    simp only [Optimization.logCost]
    rw [show (1-(1/2 : ℝ)) = (2:ℝ)⁻¹ by norm_num,log_inv,neg_neg]
  simp only [Optimization.energy,Fin.sum_univ_castSucc,fillMatrix_active,
    fillMatrix_last_right,fillMatrix_last_left,hc,sum_add_distrib]
  simp only [← sum_mul,← mul_sum]
  have hs' : (∑ i : Fin m, α i.castSucc) = 1-α (Fin.last m) := by linarith only [hs]
  rw [hs']
  ring

theorem fillMatrix_energy_bound {m : ℕ} (α : Fin (m+1) → ℝ)
    (hα : ∑ i, α i = 1) (q : Fin m → Fin m → ℝ) :
    Optimization.energy α (fillMatrix q) ≤
      Optimization.energy (fun i => α i.castSucc) q + 2*α (Fin.last m)*log 2 := by
  rw [fillMatrix_energy α hα q]
  have hh := mul_nonneg (sq_nonneg (α (Fin.last m))) (log_nonneg (by norm_num : (1:ℝ)≤2))
  nlinarith only [hh]

end HadwigerRamsey.Main
