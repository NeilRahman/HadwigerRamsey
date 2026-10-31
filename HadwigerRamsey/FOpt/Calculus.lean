import HadwigerRamsey.FOpt.Definitions
import HadwigerRamsey.FOpt.Algebra

namespace HadwigerRamsey.FOpt
open Real Set
set_option maxHeartbeats 1000000

noncomputable def first (c x : ℝ) : ℝ :=
  2*x*(log (2-exp (-(c/x^2))) - c/x^2*exp (-(c/x^2))/(2-exp (-(c/x^2))))
noncomputable def second (c x : ℝ) : ℝ :=
  2*log (2-exp (-(c/x^2))) - 2*(c/x^2)*exp (-(c/x^2))/(2-exp (-(c/x^2))) -
    8*(c/x^2)^2*exp (-(c/x^2))/(2-exp (-(c/x^2)))^2

lemma log_argument_pos {c x : ℝ} (hc : 0 ≤ c) : 0 < 2-exp (-(c/x^2)) := by
  have h : exp (-(c/x^2)) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hc (sq_nonneg x)))
  linarith

lemma hasDerivAt_value {c x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    HasDerivAt (value c) (first c x) x := by
  have harg := log_argument_pos (x := x) hc
  have ht := (hasDerivAt_const x c).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  have he := ht.neg.exp
  have hd := (hasDerivAt_const x (2 : ℝ)).sub he
  have hl := hd.log (by simpa using harg.ne')
  have hf := ((hasDerivAt_id x).pow 2).mul hl
  convert! hf using 1
  all_goals first | rfl | (dsimp [value,first]; field_simp [hx,harg.ne']; ring)

lemma hasDerivAt_first {c x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    HasDerivAt (first c) (second c x) x := by
  have harg := log_argument_pos (x := x) hc
  have ht := (hasDerivAt_const x c).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  have he := ht.neg.exp
  have hd := (hasDerivAt_const x (2 : ℝ)).sub he
  have hl := hd.log (by simpa using harg.ne')
  have hfirst := ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)).mul
    (hl.sub ((ht.mul he).div hd (by simpa using harg.ne')))
  convert! hfirst using 1
  all_goals first | rfl | (dsimp [first,second]; field_simp [hx,harg.ne']; ring)

noncomputable def gap (x : ℝ) : ℝ := cubic F a x - value c x
noncomputable def gapFirst (x : ℝ) : ℝ := F + a*(-3*x^2+3*x-1/2) - first c x

lemma hasDerivAt_gap {x : ℝ} (hx : x ≠ 0) : HasDerivAt gap (gapFirst x) x := by
  have hp : HasDerivAt (cubic F a) (F + a*(-3*x^2+3*x-1/2)) x := by
    have h := ((hasDerivAt_const x F).mul (hasDerivAt_id x)).add
      ((((hasDerivAt_const x a).mul (hasDerivAt_id x)).mul
        ((hasDerivAt_id x).sub_const (1/2))).mul
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)))
    convert! h using 1
    all_goals first | rfl | (dsimp; ring)
  exact hp.sub (hasDerivAt_value c_pos.le hx)

lemma hasDerivAt_gapFirst {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt gapFirst (a*(3-6*x) - second c x) x := by
  have hp := (hasDerivAt_const x F).add
    ((hasDerivAt_const x a).mul
      (((((hasDerivAt_id x).pow 2).const_mul (-3)).add
        ((hasDerivAt_id x).const_mul 3)).sub_const (1/2)))
  convert! hp.sub (hasDerivAt_first c_pos.le hx) using 1
  all_goals first | rfl | (dsimp [gapFirst]; ring)

lemma gap_half : gap (1/2) = 0 := by rw [gap,value_half]; dsimp [cubic]; ring

lemma gapFirst_half : gapFirst (1/2) = 0 := by
  dsimp [gapFirst,first]
  norm_num
  rw [show -(c/(1/4 : ℝ)) = -4*c by ring,
    show c/(1/4 : ℝ) = 4*c by ring,exp_neg_four_c]
  have hh : log (2-q) = 2*F := by rw [← exp_neg_four_c, log_half_identity]
  rw [hh]
  dsimp [a]
  field_simp
  <;> ring

end HadwigerRamsey.FOpt
