import HadwigerRamsey4Col.ThresholdBounds

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

lemma ball_quadratic_bound {s : ℝ} (_hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ballA-ballK ≤ ballA*s^2+2*ballB*(1-s)*s+ballC*(1-s)^2-ballK*s := by
  obtain ⟨hAB,hC,hK,_⟩ := ball_constants
  have hh := mul_nonneg (sub_nonneg.mpr hs1)
    (show 0 ≤ ballK-2*(ballA-ballB)+(ballA-2*ballB+ballC)*(1-s) by positivity)
  nlinarith

lemma ball_large_arm {z : ℝ} {x : Fin 4 → ℝ}
    (hz : 0 ≤ z) (hx : ∀ c, 0 ≤ x c) (hs : z+∑ c, x c=1)
    (he : ballA*(∑ c,x c)^2+(ballB-ballA)*(∑ c,(x c)^2)+
      2*ballB*z*(∑ c,x c)+ballC*z^2-ballK*(∑ c,x c) ≤ 4*threshold) :
    ∃ c, (33/50 : ℝ)<x c := by
  by_contra! hn
  have hS : 0 ≤ ∑ c,x c := sum_nonneg (fun c _ => hx c)
  have hS1 : ∑ c,x c ≤ 1 := by linarith
  have hQ : ∑ c,(x c)^2 ≤ (33/50 : ℝ) := by
    calc
      _ ≤ ∑ c, (33/50 : ℝ)*x c := sum_le_sum (fun c _ => by nlinarith [hx c,hn c])
      _ = (33/50 : ℝ)*∑ c,x c := (mul_sum ..).symm
      _ ≤ 33/50 := by linarith
  have hb := ball_quadratic_bound hS hS1
  have hm := mul_le_mul_of_nonneg_left hQ ball_constants.1.le
  have hk := ball_constants.2.2.2
  have hzz : z=1-∑ c,x c := by linarith
  rw [hzz] at he
  have hh : (17/50 : ℝ)*ballA+(33/50 : ℝ)*ballB ≤ ballK+4*threshold := by
    linear_combination he+hm+hb
  linarith

end HadwigerRamsey4Col
