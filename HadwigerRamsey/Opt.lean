import HadwigerRamsey.FOpt

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey

lemma beta_pos : 0 < beta := by
  have hs : beta^2 = FOpt.c := FOpt.beta_sq
  have hn : 0 ≤ beta := by dsimp [beta,FOpt.beta]; positivity
  nlinarith [FOpt.c_pos]

namespace Optimization

/-- The nonnegative logarithmic cost of a probability strictly below one. -/
noncomputable def logCost (p : ℝ) : ℝ := -log (1-p)

/-- The double sum appearing under the square roots in Lemma 3.8. -/
noncomputable def energy {k : ℕ} (α : Fin k → ℝ) (q : Fin k → Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, α i * α j * logCost (q i j)

lemma logCost_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : 0 ≤ logCost p := by
  dsimp [logCost]
  have := log_nonpos (by linarith : 0 ≤ 1-p) (by linarith : 1-p ≤ 1)
  linarith

lemma logCost_mono {p q : ℝ} (hpq : p ≤ q) (hq : q < 1) : logCost p ≤ logCost q := by
  dsimp [logCost]
  have := log_le_log (by linarith : 0 < 1-q) (by linarith : 1-q ≤ 1-p)
  linarith

lemma logCost_midpoint {p q : ℝ} (hp : p < 1) (hq : q < 1) :
    logCost ((p+q)/2) ≤ (logCost p + logCost q)/2 := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show 1-p ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
    (show 1-q ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+1/2 = 1)
  simp only [smul_eq_mul] at h
  rw [show (1/2 : ℝ)*(1-p)+(1/2)*(1-q) = 1-(p+q)/2 by ring] at h
  dsimp [logCost]
  linarith

lemma energy_eq_neg_sum {k : ℕ} (α : Fin k → ℝ) (q : Fin k → Fin k → ℝ) :
    energy α q = -(∑ i, ∑ j, α i * α j * log (1-q i j)) := by
  simp [energy,logCost,Finset.sum_neg_distrib]

lemma energy_nonneg {k : ℕ} {α : Fin k → ℝ} {q : Fin k → Fin k → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hq0 : ∀ i j, 0 ≤ q i j) (hq1 : ∀ i j, q i j < 1) :
    0 ≤ energy α q :=
  sum_nonneg (fun i _ => sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hα i) (hα j)) (logCost_nonneg (hq0 i j) (hq1 i j))))

/-- The logarithmic lower bound behind Lemma 3.8; one-sided mass constraints suffice. -/
lemma energy_average_lower {k : ℕ} (α p : Fin k → ℝ) (qB qG : Fin k → Fin k → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1) (hp0 : ∀ i, 0 ≤ p i)
    (hB : ∀ i j, qB i j < 1) (hG : ∀ i j, qG i j < 1)
    (hdiag : ∀ i, 1 ≤ p i + qB i i + qG i i)
    (hoff : ∀ i j, i ≠ j → 1 ≤ qB i j + qG i j) :
    log 2 - ∑ i, (α i)^2 * log (1+p i) ≤ (energy α qB + energy α qG)/2 := by
  have hpoint (i j : Fin k) :
      log 2 - (if i = j then log (1+p i) else 0) ≤
        (logCost (qB i j)+logCost (qG i j))/2 := by
    apply le_trans _ (logCost_midpoint (hB i j) (hG i j))
    by_cases hij : i = j
    · subst j
      have hm := logCost_mono (show (1-p i)/2 ≤ (qB i i+qG i i)/2 by linarith [hdiag i])
        (show (qB i i+qG i i)/2 < 1 by linarith [hB i i,hG i i])
      have he : logCost ((1-p i)/2) = log 2 - log (1+p i) := by
        dsimp [logCost]
        rw [show 1-(1-p i)/2 = (1+p i)/2 by ring,
          log_div (by linarith [hp0 i]) (by norm_num)]
        ring
      simpa [he] using hm
    · have hm := logCost_mono (show (1/2 : ℝ) ≤ (qB i j+qG i j)/2 by linarith [hoff i j hij])
        (show (qB i j+qG i j)/2 < 1 by linarith [hB i j,hG i j])
      have he : logCost (1/2) = log 2 := by norm_num [logCost,log_div]
      simpa only [if_neg hij,sub_zero,he] using hm
  have hsum := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (hpoint i j) (mul_nonneg (hα i) (hα j))))
  have hmass : (∑ i, ∑ j, α i * α j) = 1 := by
    simp only [← mul_sum,hs,mul_one]
  have hleft : (∑ i, ∑ j, α i * α j * (log 2 - (if i = j then log (1+p i) else 0))) =
      log 2 - ∑ i, (α i)^2*log (1+p i) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← sum_mul,hmass,one_mul]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp [mul_ite,pow_two]
  have hright : (∑ i, ∑ j, α i * α j * ((logCost (qB i j)+logCost (qG i j))/2)) =
      (energy α qB+energy α qG)/2 := by
    simp only [energy,← mul_div_assoc,mul_add,← Finset.sum_div,Finset.sum_add_distrib]
  rwa [hleft,hright] at hsum

/-- The diagonal estimate, with a separate zero-weight case. -/
lemma diagonal_le_function {x p : ℝ} (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hsmall : x * sqrt (logCost p) < beta) :
    x^2 * log (1+p) ≤ optimizationFunction x := by
  by_cases hz : x = 0
  · simp [hz]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hcost := logCost_nonneg hp0 hp1
  have hsq : x^2 * logCost p < beta^2 := by
    have ht := (sq_lt_sq₀ (mul_nonneg hx (sqrt_nonneg _)) beta_pos.le).mpr hsmall
    rwa [mul_pow,sq_sqrt hcost] at ht
  have hlog : -(beta^2/x^2) ≤ log (1-p) := by
    rw [← neg_div]
    apply (div_le_iff₀ (sq_pos_of_pos hxpos)).mpr
    dsimp [logCost] at hsq
    linarith
  have he : exp (-(beta^2/x^2)) ≤ 1-p := (le_log_iff_exp_le (by linarith)).mp hlog
  have hlogs : log (1+p) ≤ log (2-exp (-(beta^2/x^2))) :=
    log_le_log (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left hlogs (sq_nonneg x)

/-- A strengthened form of Lemma 3.8, allowing zero weights and one-sided mass constraints. -/
theorem opt_of_nonneg (k : ℕ) (α p : Fin k → ℝ) (qB qG : Fin k → Fin k → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hB0 : ∀ i j, 0 ≤ qB i j) (hB1 : ∀ i j, qB i j < 1)
    (hG0 : ∀ i j, 0 ≤ qG i j) (hG1 : ∀ i j, qG i j < 1)
    (hdiag : ∀ i, 1 ≤ p i + qB i i + qG i i)
    (hoff : ∀ i j, i ≠ j → 1 ≤ qB i j + qG i j) :
    (∃ i, beta ≤ α i * sqrt (logCost (p i))) ∨
      beta ≤ sqrt (energy α qB) ∨ beta ≤ sqrt (energy α qG) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hp,hB,hG⟩ := hn
  have hEB : energy α qB < beta^2 :=
    (sqrt_lt (energy_nonneg hα hB0 hB1) beta_pos.le).mp hB
  have hEG : energy α qG < beta^2 :=
    (sqrt_lt (energy_nonneg hα hG0 hG1) beta_pos.le).mp hG
  have hlow := energy_average_lower α p qB qG hα hs hp0 hB1 hG1 hdiag hoff
  have hsum : (∑ i, (α i)^2 * log (1+p i)) ≤ ∑ i, optimizationFunction (α i) :=
    sum_le_sum (fun i _ => diagonal_le_function (hα i) (hp0 i) (hp1 i) (hp i))
  have hf := fopt k α hα hs
  linarith

end Optimization
/-- Lemma 3.8, with the hypotheses and alternatives of the manuscript. -/
theorem opt (k : ℕ) (α p : Fin k → ℝ) (qB qG : Fin k → Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hs : ∑ i, α i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hB0 : ∀ i j, 0 ≤ qB i j) (hB1 : ∀ i j, qB i j < 1)
    (hG0 : ∀ i j, 0 ≤ qG i j) (hG1 : ∀ i j, qG i j < 1)
    (hdiag : ∀ i, p i + qB i i + qG i i = 1)
    (hoff : ∀ i j, i ≠ j → qB i j + qG i j = 1) :
    (∃ i, beta ≤ α i * sqrt (-log (1-p i))) ∨
      beta ≤ sqrt (-(∑ i, ∑ j, α i * α j * log (1-qB i j))) ∨
      beta ≤ sqrt (-(∑ i, ∑ j, α i * α j * log (1-qG i j))) := by
  simpa only [Optimization.logCost,Optimization.energy_eq_neg_sum] using
    Optimization.opt_of_nonneg k α p qB qG (fun i => (hα i).le) hs hp0 hp1
      hB0 hB1 hG0 hG1 (fun i => (hdiag i).ge) (fun i j hij => (hoff i j hij).ge)

end HadwigerRamsey
