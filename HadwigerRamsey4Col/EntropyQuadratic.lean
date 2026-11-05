import HadwigerRamsey4Col.Entropy

open Real Set
namespace HadwigerRamsey4Col

/-- A polynomial correction that makes the entropy remainder convex on the
required interval. Its constant and linear terms vanish at zero. -/
noncomputable def correctedEntropy (w d : ℝ) : ℝ :=
  entropy (w+d)-entropy w-entropySlope w*d+
    (3/2 : ℝ)*d^2-(3/2 : ℝ)*d^3+(25/6 : ℝ)*d^4

noncomputable def correctedEntropySlope (w d : ℝ) : ℝ :=
  entropySlope (w+d)-entropySlope w+3*d-(9/2 : ℝ)*d^2+(50/3 : ℝ)*d^3

lemma correctedEntropy_hasDerivAt {w d : ℝ} (hx : 0 < w+d) :
    HasDerivAt (correctedEntropy w) (correctedEntropySlope w d) d := by
  have hH := (entropy_hasDerivAt hx).comp d ((hasDerivAt_id d).const_add w)
  have h := ((((hH.sub_const (entropy w)).sub
    ((hasDerivAt_id d).const_mul (entropySlope w))).add
    (((hasDerivAt_id d).pow 2).const_mul (3/2))).sub
    (((hasDerivAt_id d).pow 3).const_mul (3/2))).add
    (((hasDerivAt_id d).pow 4).const_mul (25/6))
  change HasDerivAt (fun y => entropy (w+y)-entropy w-entropySlope w*y+
    (3/2 : ℝ)*y^2-(3/2 : ℝ)*y^3+(25/6 : ℝ)*y^4) _ d
  apply h.congr_deriv
  norm_num [correctedEntropySlope]
  ring

lemma correctedEntropySlope_hasDerivAt {w d : ℝ} (hx : 0 < w+d) :
    HasDerivAt (correctedEntropySlope w)
      (-1/((w+d)*(1+(w+d)))+3-9*d+50*d^2) d := by
  have hH := (entropySlope_hasDerivAt hx).comp d ((hasDerivAt_id d).const_add w)
  have h := ((((hH.sub_const (entropySlope w)).add
    ((hasDerivAt_id d).const_mul 3)).sub
    (((hasDerivAt_id d).pow 2).const_mul (9/2))).add
    (((hasDerivAt_id d).pow 3).const_mul (50/3)))
  change HasDerivAt (fun y => entropySlope (w+y)-entropySlope w+3*y-
    (9/2 : ℝ)*y^2+(50/3 : ℝ)*y^3) _ d
  apply h.congr_deriv
  norm_num
  ring

lemma correctedEntropy_curvature {w d : ℝ} (hw : (1/3 : ℝ) ≤ w)
    (hd : d ∈ Icc (-3/20 : ℝ) (3/20)) :
    0 ≤ -1/((w+d)*(1+(w+d)))+3-9*d+50*d^2 := by
  have hx : 0 < w+d := by linarith [hd.1]
  have hx0 : 0 < (1/3 : ℝ)+d := by linarith [hd.1]
  let q : ℝ := 3-9*d+50*d^2
  have hq : 0 ≤ q := by dsimp [q]; nlinarith [sq_nonneg (d-9/100)]
  have hsq := mul_nonneg (sq_nonneg d) (show (0:ℝ) ≤ 23/3+50*d by linarith [hd.1])
  have hbase : 1 ≤ q*((1/3 : ℝ)+d) := by dsimp [q]; nlinarith
  have hqmul : 1 ≤ q*(w+d) := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hw)]
  have hden : 0 < (w+d)*(1+(w+d)) := by positivity
  have hdenmul : 1 ≤ q*((w+d)*(1+(w+d))) := by
    have hpos := mul_nonneg hq (sq_nonneg (w+d))
    nlinarith
  have hi : 1/((w+d)*(1+(w+d))) ≤ q := (div_le_iff₀ hden).mpr (by nlinarith)
  dsimp [q] at hi
  rw [neg_div]
  linarith

/-- The entropy quadratic lower bound, uniformly for every `w ≥ 1/3`. -/
theorem entropy_quadratic_lower {w d : ℝ} (hw : (1/3 : ℝ) ≤ w)
    (hd : |d| ≤ (3/20 : ℝ)) :
    entropy w+entropySlope w*d-2*d^2 ≤ entropy (w+d) := by
  have hdI : d ∈ Icc (-3/20 : ℝ) (3/20) := by simpa [neg_div] using abs_le.mp hd
  have hpos : ∀ t ∈ Icc (-3/20 : ℝ) (3/20), 0 < w+t := by
    intro t ht
    linarith [ht.1]
  have hc : ConvexOn ℝ (Icc (-3/20 : ℝ) (3/20)) (correctedEntropy w) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (f' := correctedEntropySlope w)
      (f'' := fun t => -1/((w+t)*(1+(w+t)))+3-9*t+50*t^2)
    · intro t ht
      exact (correctedEntropy_hasDerivAt (hpos t ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact (correctedEntropy_hasDerivAt (hpos t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact (correctedEntropySlope_hasDerivAt (hpos t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact correctedEntropy_curvature hw (interior_subset ht)
  have hz : HasDerivAt (correctedEntropy w) 0 0 := by
    convert correctedEntropy_hasDerivAt (hpos 0 (by norm_num)) using 1
    simp [correctedEntropySlope]
  have hmin := hc.isMinOn_of_rightDeriv_eq_zero
    (show (0:ℝ) ∈ interior (Icc (-3/20 : ℝ) (3/20)) by norm_num [interior_Icc])
    (hz.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0))
  have hh := hmin hdI
  change correctedEntropy w 0 ≤ correctedEntropy w d at hh
  simp [correctedEntropy] at hh
  have hd2 : d^2 ≤ (9/400 : ℝ) := by nlinarith [hdI.1,hdI.2]
  have hbr : 0 ≤ (1/2 : ℝ)+(3/2 : ℝ)*d-(25/6 : ℝ)*d^2 := by nlinarith [hdI.1]
  have hprod := mul_nonneg (sq_nonneg d) hbr
  nlinarith

end HadwigerRamsey4Col
