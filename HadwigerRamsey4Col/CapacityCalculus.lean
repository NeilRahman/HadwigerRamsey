import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Real Set
namespace HadwigerRamsey4Col

lemma sqrt_quotient_algebra (v df z r : ℝ) (hr : r^2=z) (hr0 : r ≠ 0) :
    (df*r-v*(1/(2*r)))/r^2 = (2*z*df-v)/(2*z*r) := by
  rw [← hr]
  field_simp

lemma normalized_hasDerivAt {f : ℝ → ℝ} {df z : ℝ} (hz : 0 < z)
    (hf : HasDerivAt f df z) :
    HasDerivAt (fun x => f x/sqrt x) ((2*z*df-f z)/(2*z*sqrt z)) z := by
  have hs := hasDerivAt_sqrt (ne_of_gt hz)
  have hr0 : sqrt z ≠ 0 := ne_of_gt (sqrt_pos.mpr hz)
  apply (hf.div hs hr0).congr_deriv
  exact sqrt_quotient_algebra (f z) df z (sqrt z) (sq_sqrt hz.le) hr0

/-- A bound on `2 sqrt(z) f'(z)` bounds the square-root-normalized function,
provided its derivative has the correct sign up to the chosen anchor. -/
theorem capacity_bound_of_anchor {f df : ℝ → ℝ} {a C : ℝ} (ha : 0 < a)
    (hf : ∀ z, 0 < z → HasDerivAt f (df z) z)
    (hhead : ∀ z ∈ Icc 0 a, 0 ≤ 2*z*df z-f z)
    (htail : ∀ z, a ≤ z → 2*sqrt z*df z ≤ C) :
    ∀ z, 0 < z → f z ≤ C*sqrt z := by
  have hfa : f a ≤ C*sqrt a := by
    have hg := hhead a ⟨ha.le,le_rfl⟩
    have hh := mul_le_mul_of_nonneg_right (htail a le_rfl) (sqrt_nonneg a)
    have he : 2*sqrt a*df a*sqrt a = 2*a*df a := by
      calc
        _ = 2*df a*(sqrt a)^2 := by ring
        _ = _ := by rw [sq_sqrt ha.le]; ring
    rw [he] at hh
    linarith
  intro z hz
  by_cases hza : z ≤ a
  · have hmono : MonotoneOn (fun x => f x/sqrt x) (Icc z a) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (f' := fun x => (2*x*df x-f x)/(2*x*sqrt x))
      · intro x hx
        exact (normalized_hasDerivAt (lt_of_lt_of_le hz hx.1) (hf x (lt_of_lt_of_le hz hx.1))).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (normalized_hasDerivAt (lt_of_lt_of_le hz hx'.1) (hf x (lt_of_lt_of_le hz hx'.1))).hasDerivWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact div_nonneg (hhead x ⟨(hz.trans_le hx'.1).le,hx'.2⟩)
          (by have hx0 := hz.trans_le hx'.1; have := sqrt_nonneg x; positivity)
    have hh := hmono ⟨le_rfl,hza⟩ ⟨hza,le_rfl⟩ hza
    have hh' : f a/sqrt a ≤ C := (div_le_iff₀ (sqrt_pos.mpr ha)).mpr hfa
    exact (div_le_iff₀ (sqrt_pos.mpr hz)).mp (hh.trans hh')
  · have haz : a ≤ z := (le_of_not_ge hza)
    have hanti : AntitoneOn (fun x => f x-C*sqrt x) (Icc a z) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (f' := fun x => df x-C*(1/(2*sqrt x)))
      · intro x hx
        have hx0 := lt_of_lt_of_le ha hx.1
        exact ((hf x hx0).sub ((hasDerivAt_sqrt (ne_of_gt hx0)).const_mul C)).continuousAt.continuousWithinAt
      · intro x hx
        have hx0 := lt_of_lt_of_le ha (interior_subset hx).1
        exact ((hf x hx0).sub ((hasDerivAt_sqrt (ne_of_gt hx0)).const_mul C)).hasDerivWithinAt
      · intro x hx
        have hx' := interior_subset hx
        have hs : 0 < 2*sqrt x := by have := sqrt_pos.mpr (ha.trans_le hx'.1); positivity
        have hh : df x ≤ C/(2*sqrt x) := (le_div_iff₀ hs).mpr (by nlinarith [htail x hx'.1])
        simp only [div_eq_mul_inv, one_mul] at hh ⊢
        linarith
    have hh := hanti ⟨le_rfl,haz⟩ ⟨haz,le_rfl⟩ haz
    linarith

/-- Monotonicity of the auxiliary derivative bound after the anchor. -/
theorem sqrt_derivative_antitone {df ddf : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : ∀ z, a ≤ z → HasDerivAt df (ddf z) z)
    (hsign : ∀ z, a ≤ z → df z+2*z*ddf z ≤ 0) :
    AntitoneOn (fun z => 2*sqrt z*df z) (Ici a) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (f' := fun z => 2*(1/(2*sqrt z))*df z+2*sqrt z*ddf z)
  · intro z hz
    have hz0 := ha.trans_le hz
    exact (((hasDerivAt_sqrt (ne_of_gt hz0)).const_mul 2).mul (hf z hz)).continuousAt.continuousWithinAt
  · intro z hz
    have hz' := interior_subset hz
    have hz0 := ha.trans_le hz'
    exact (((hasDerivAt_sqrt (ne_of_gt hz0)).const_mul 2).mul (hf z hz')).hasDerivWithinAt
  · intro z hz
    have hz' := interior_subset hz
    have hz0 := ha.trans_le hz'
    have hr : 0 < sqrt z := sqrt_pos.mpr hz0
    have he : 2*(1/(2*sqrt z))*df z+2*sqrt z*ddf z =
        (df z+2*z*ddf z)/sqrt z := by
      apply (eq_div_iff (ne_of_gt hr)).mpr
      calc
        _ = df z+2*(sqrt z)^2*ddf z := by field_simp
        _ = _ := by rw [sq_sqrt hz0.le]
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (hsign z hz') hr.le

end HadwigerRamsey4Col
