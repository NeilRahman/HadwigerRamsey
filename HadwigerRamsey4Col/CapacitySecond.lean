import HadwigerRamsey4Col.CapacityLog

open Real Set
namespace HadwigerRamsey4Col

lemma capacityLogTest_anchor_pos : 0 < capacityLogTest (41/40 : ℝ) := by
  obtain ⟨hl,hu⟩ := exp_second_anchor
  have hden := capacity_den_pos (show (0:ℝ) ≤ 41/40 by norm_num)
  have hi := one_div_lt_one_div_of_lt (exp_pos (41/40 : ℝ)) hu
  norm_num at hi
  have harg : (3-exp (-(41/40 : ℝ)))/2 < (73613/55742 : ℝ) := by
    rw [exp_neg]
    linarith
  have hlog := log_lt_log (capacity_arg_pos (show (0:ℝ) ≤ 41/40 by norm_num)) harg
  have hlog' : capacityLog (41/40 : ℝ) < (1391/5000 : ℝ) :=
    hlog.trans log_second_anchor_bound
  have hrat : (20500/73613 : ℝ) < 2*(41/40 : ℝ)/(3*exp (41/40 : ℝ)-1) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  dsimp [capacityLogTest]
  linarith

lemma capacityLogTest_nonneg {z : ℝ} (hz : z ∈ Icc 0 (41/40 : ℝ)) :
    0 ≤ capacityLogTest z := by
  have h0 : capacityLogTest 0 = 0 := by norm_num [capacityLogTest, capacityLog]
  have ha := capacityLogTest_anchor_pos.le
  have hh := capacityLogTest_concave.min_le_of_mem_Icc
    (show (0:ℝ) ∈ Icc 0 (41/40 : ℝ) by norm_num)
    (show (41/40 : ℝ) ∈ Icc 0 (41/40 : ℝ) by norm_num) hz
  rw [h0, min_eq_left ha] at hh
  exact hh

lemma second_anchor_derivative_bound :
    2*sqrt (41/40 : ℝ)*(3*(1/(3*exp (41/40 : ℝ)-1))) ≤ (413/500 : ℝ) := by
  have hs : sqrt (41/40 : ℝ) < (81/80 : ℝ) := by
    have := sq_sqrt (show (0:ℝ) ≤ 41/40 by norm_num)
    have := sqrt_nonneg (41/40 : ℝ)
    nlinarith
  have hl := exp_second_anchor.1
  have hden := capacity_den_pos (show (0:ℝ) ≤ 41/40 by norm_num)
  have he : 2*sqrt (41/40 : ℝ)*(3*(1/(3*exp (41/40 : ℝ)-1))) =
      6*sqrt (41/40 : ℝ)/(3*exp (41/40 : ℝ)-1) := by ring
  rw [he]
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- The second normalized capacity inequality. -/
theorem second_normalized_capacity {z : ℝ} (hz : 0 < z) :
    3*log ((3-exp (-z))/2) ≤ (413/500 : ℝ)*sqrt z := by
  apply capacity_bound_of_anchor (f := fun x => 3*capacityLog x)
    (a := (41/40 : ℝ)) (df := fun x => 3*(1/(3*exp x-1))) (by norm_num)
  · intro x hx
    exact (capacityLog_hasDerivAt hx.le).const_mul 3
  · intro x hx
    have hh := mul_nonneg (show (0:ℝ) ≤ 3 by norm_num) (capacityLogTest_nonneg hx)
    dsimp [capacityLogTest] at hh
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  · have hanti : AntitoneOn (fun x => 2*sqrt x*(3*(1/(3*exp x-1))))
        (Ici (41/40 : ℝ)) := by
      apply sqrt_derivative_antitone (by norm_num : (0:ℝ)<41/40)
        (ddf := fun x => 3*(-3*exp x/(3*exp x-1)^2))
      · intro x hx
        exact (capacityLog_derivative_hasDerivAt (show 0 ≤ x by linarith)).const_mul 3
      · intro x hx
        have he := exp_pos x
        have hden := capacity_den_pos (show 0 ≤ x by linarith)
        have hn : 3*exp x*(1-2*x)-1 ≤ 0 := by nlinarith
        have hid : 3*(1/(3*exp x-1))+2*x*(3*(-3*exp x/(3*exp x-1)^2)) =
            3*(3*exp x*(1-2*x)-1)/(3*exp x-1)^2 := by
          field_simp [ne_of_gt hden]
          ring
        rw [hid]
        exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hn)
          (sq_nonneg _)
    intro x hx
    exact (hanti (show (41/40 : ℝ) ∈ Ici (41/40 : ℝ) by norm_num) hx hx).trans
      second_anchor_derivative_bound
  · exact hz

end HadwigerRamsey4Col
