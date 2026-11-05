import HadwigerRamsey4Col.CapacityFirst
import HadwigerRamsey4Col.CapacitySecond

open Real
namespace HadwigerRamsey4Col

/-- The first capacity function. The formula also has value zero at `s = 0`. -/
noncomputable def capacityF (t s : ℝ) : ℝ := s^2*(1-exp (-(t/s^2)))
/-- The second capacity function, including the zero-mass convention. -/
noncomputable def capacityG (t s : ℝ) : ℝ := 3*s^2*log ((3-exp (-(t/s^2)))/2)

@[simp] theorem capacityF_zero (t : ℝ) : capacityF t 0 = 0 := by simp [capacityF]
@[simp] theorem capacityG_zero (t : ℝ) : capacityG t 0 = 0 := by simp [capacityG]

lemma capacity_sqrt_scale {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    s^2*sqrt (t/s^2) = sqrt t*s := by
  rw [sqrt_div ht, sqrt_sq hs.le]
  field_simp

/-- The first capacity inequality in Lemma 6. -/
theorem capacityF_bound {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    capacityF t s ≤ (16/25 : ℝ)*sqrt t*s := by
  rcases eq_or_lt_of_le hs with he | hs
  · subst s
    simp
  have hz : 0 < t/s^2 := div_pos ht (sq_pos_of_pos hs)
  have hh := mul_le_mul_of_nonneg_left (first_normalized_capacity hz) (sq_nonneg s)
  calc
    capacityF t s ≤ s^2*((16/25 : ℝ)*sqrt (t/s^2)) := hh
    _ = (16/25 : ℝ)*(s^2*sqrt (t/s^2)) := by ring
    _ = (16/25 : ℝ)*sqrt t*s := by rw [capacity_sqrt_scale ht.le hs]; ring

/-- The second capacity inequality in Lemma 6. -/
theorem capacityG_bound {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    capacityG t s ≤ (413/500 : ℝ)*sqrt t*s := by
  rcases eq_or_lt_of_le hs with he | hs
  · subst s
    simp
  have hz : 0 < t/s^2 := div_pos ht (sq_pos_of_pos hs)
  have hh := mul_le_mul_of_nonneg_left (second_normalized_capacity hz) (sq_nonneg s)
  calc
    capacityG t s = s^2*(3*log ((3-exp (-(t/s^2)))/2)) := by unfold capacityG; ring
    _ ≤ s^2*((413/500 : ℝ)*sqrt (t/s^2)) := hh
    _ = (413/500 : ℝ)*(s^2*sqrt (t/s^2)) := by ring
    _ = (413/500 : ℝ)*sqrt t*s := by rw [capacity_sqrt_scale ht.le hs]; ring

end HadwigerRamsey4Col
