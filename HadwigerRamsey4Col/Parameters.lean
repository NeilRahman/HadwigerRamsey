import HadwigerRamsey4Col.Analytic

namespace HadwigerRamsey4Col

/-- The algebraic parameter in the analytic manuscript exists uniquely in `(0,1)`. -/
theorem exists_unique_parameter :
    ∃! p : ℝ, 0 < p ∧ p < 1 ∧ 3*p^6+2*p-2=0 := by
  let f : ℝ → ℝ := fun p => 3*p^6+2*p-2
  have hc : ContinuousOn f (Set.Icc 0 1) := by fun_prop
  obtain ⟨p,hp,hfp⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hc
    (show (0:ℝ) ∈ Set.Icc (f 0) (f 1) by norm_num [f])
  have hp0 : 0 < p := by
    have := hp.1
    dsimp [f] at hfp
    rcases eq_or_lt_of_le this with h | h
    · rw [← h] at hfp
      norm_num at hfp
    · exact h
  have hp1 : p < 1 := by
    have := hp.2
    dsimp [f] at hfp
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · rw [h] at hfp
      norm_num at hfp
  refine ⟨p,⟨hp0,hp1,hfp⟩,?_⟩
  rintro q ⟨hq0,hq1,hq⟩
  dsimp [f] at hfp
  rcases lt_trichotomy q p with h | h | h
  · have := pow_le_pow_left₀ hq0.le h.le 6
    nlinarith
  · exact h
  · have := pow_le_pow_left₀ hp0.le h.le 6
    nlinarith

noncomputable def parameter : ℝ := Classical.choose exists_unique_parameter.exists

theorem parameter_spec :
    0 < parameter ∧ parameter < 1 ∧ 3*parameter^6+2*parameter-2=0 :=
  Classical.choose_spec exists_unique_parameter.exists

end HadwigerRamsey4Col
