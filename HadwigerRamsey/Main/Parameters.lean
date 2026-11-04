import HadwigerRamsey.Main.Analytic

open Real
namespace HadwigerRamsey.Main

theorem choose_lam {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1/100 ∧ lam ≤ ε*beta/100 ∧
      42*lam*log 2 ≤ ε*beta^2/10 := by
  let lam := min (1/1000 : ℝ) (min (ε*beta/1000) (ε*beta^2/10000))
  have hb := beta_pos
  have hl : 0 < lam := by dsimp [lam]; positivity
  have h1 : lam ≤ 1/1000 := min_le_left _ _
  have h2 : lam ≤ ε*beta/1000 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : lam ≤ ε*beta^2/10000 := (min_le_right _ _).trans (min_le_right _ _)
  have hlog : log (2:ℝ) ≤ 1 := by have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hh := mul_le_mul_of_nonneg_left hlog (show 0≤42*lam by positivity)
  refine ⟨lam,hl,by linarith,by nlinarith only [h2,mul_pos hε hb],?_⟩
  have hεβ : 0 < ε*beta^2 := by positivity
  nlinarith only [hh,h3,hεβ]

theorem choose_small {ε lam ζ ξ : ℝ} (hε : 0 < ε) (hl : 0 < lam)
    (hz : 0 < ζ) (hx : 0 < ξ) :
    ∃ e η : ℝ, 0 < e ∧ 0 < η ∧ e ≤ lam*ξ/100 ∧
      e ≤ lam*ε/100 ∧ e ≤ ζ*beta^2/100 ∧ η/lam ≤ ξ/4 := by
  let e := min (lam*ξ) (min (lam*ε) (ζ*beta^2))/100
  let η := lam*ξ/4
  have he : 0 < e := by dsimp [e]; have := beta_pos; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨e,η,he,hη,?_,?_,?_,?_⟩
  · exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  · exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  · exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  · dsimp [η]
    field_simp
    norm_num

end HadwigerRamsey.Main
