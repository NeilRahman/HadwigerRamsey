import HadwigerRamsey4Col.StabilityData

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

lemma three_square_cap (x y z : ℝ) (hx : x ≤ 2/5) (hy : y ≤ 2/5) (hz : z ≤ 2/5)
    (hs : x+y+z=1) : x^2+y^2+z^2 ≤ (9/25 : ℝ) := by
  have hs2 : (x+y+z)^2=1 := by rw [hs]; norm_num
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy),
    mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz),
    mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)]

lemma four_square_cap (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : a ≤ 2/5) (hb' : b ≤ 2/5) (hc' : c ≤ 2/5) (hd' : d ≤ 2/5)
    (hs : a+b+c+d=1) : a^2+b^2+c^2+d^2 ≤ (9/25 : ℝ) := by
  by_cases hab : a+b ≤ (2/5 : ℝ)
  · have hh := three_square_cap (a+b) c d hab hc' hd' (by linarith)
    nlinarith [mul_nonneg ha hb]
  by_cases hac : a+c ≤ (2/5 : ℝ)
  · have hh := three_square_cap (a+c) b d hac hb' hd' (by linarith)
    nlinarith [mul_nonneg ha hc]
  by_cases had : a+d ≤ (2/5 : ℝ)
  · have hh := three_square_cap (a+d) b c had hb' hc' (by linarith)
    nlinarith [mul_nonneg ha hd]
  by_cases hbc : b+c ≤ (2/5 : ℝ)
  · have hh := three_square_cap (b+c) a d hbc ha' hd' (by linarith)
    nlinarith [mul_nonneg hb hc]
  by_cases hbd : b+d ≤ (2/5 : ℝ)
  · have hh := three_square_cap (b+d) a c hbd ha' hc' (by linarith)
    nlinarith [mul_nonneg hb hd]
  by_cases hcd : c+d ≤ (2/5 : ℝ)
  · have hh := three_square_cap (c+d) a b hcd ha' hb' (by linarith)
    nlinarith [mul_nonneg hc hd]
  have hs2 : (a+b+c+d)^2=1 := by rw [hs]; norm_num
  have pab := mul_nonneg
    (show (0:ℝ) ≤ a+b-2/5 by linarith)
    (show (0:ℝ) ≤ 3/5-a-b by linarith)
  have pac := mul_nonneg
    (show (0:ℝ) ≤ a+c-2/5 by linarith)
    (show (0:ℝ) ≤ 3/5-a-c by linarith)
  have pad := mul_nonneg
    (show (0:ℝ) ≤ a+d-2/5 by linarith)
    (show (0:ℝ) ≤ 3/5-a-d by linarith)
  have pbc := mul_nonneg
    (show (0:ℝ) ≤ b+c-2/5 by linarith)
    (show (0:ℝ) ≤ 3/5-b-c by linarith)
  have pbd := mul_nonneg
    (show (0:ℝ) ≤ b+d-2/5 by linarith)
    (show (0:ℝ) ≤ 3/5-b-d by linarith)
  have pcd := mul_nonneg
    (show (0:ℝ) ≤ c+d-2/5 by linarith)
    (show (0:ℝ) ≤ 3/5-c-d by linarith)
  nlinarith

lemma moment_lower_bounds {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hs : ∑ i, a i = 1) : (1/4 : ℝ) ≤ moment a 2 ∧ (1/16 : ℝ) ≤ moment a 3 := by
  constructor
  · have h := sum_mul_sq_le_sq_mul_sq univ a (fun _ => (1:ℝ))
    have hh : (1:ℝ) ≤ (moment a 2)*4 := by simpa [moment, hs] using h
    linarith
  · have h : 0 ≤ ∑ i, (a i-1/4)^2*(a i+1/2) := by
      exact sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (by linarith [hn i]))
    simp [moment, Fin.sum_univ_succ] at hs h ⊢
    nlinarith

lemma moment_upper_bound {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) :
    moment a 2 ≤ (9/25 : ℝ) := by
  have h := four_square_cap (a 0) (a 1) (a 2) (a 3)
    (hn 0) (hn 1) (hn 2) (hn 3) (hu 0) (hu 1) (hu 2) (hu 3)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hs)
  simpa [moment, Fin.sum_univ_succ, add_assoc] using h

lemma centered_moment_identities {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1) :
    moment a 2 = centeredMoment a 2+1/4 ∧
    moment a 3 = centeredMoment a 3+(3/4 : ℝ)*centeredMoment a 2+1/16 ∧
    moment a 4 = centeredMoment a 4+centeredMoment a 3+
      (3/8 : ℝ)*centeredMoment a 2+1/256*4 := by
  have hs' : a 3 = 1-a 0-a 1-a 2 := by
    simp [Fin.sum_univ_succ] at hs
    linarith
  simp [moment, centeredMoment, Fin.sum_univ_succ, hs']
  constructor
  · ring
  constructor <;> ring

lemma centered_moment_bounds {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) :
    0 ≤ centeredMoment a 2 ∧ centeredMoment a 2 ≤ 11/100 ∧
    centeredMoment a 3 ≤ (3/20 : ℝ)*centeredMoment a 2 ∧
    (centeredMoment a 2)^2 ≤ 4*centeredMoment a 4 := by
  have he := centered_moment_identities hs
  refine ⟨sum_nonneg (fun i _ => sq_nonneg _), ?_, ?_, ?_⟩
  · linarith [moment_upper_bound hn hu hs, he.1]
  · have h : (∑ i, (a i-1/4)^3) ≤ ∑ i, (3/20 : ℝ)*(a i-1/4)^2 := by
      apply sum_le_sum
      intro i hi
      have := mul_nonneg (sq_nonneg (a i-1/4)) (show 0 ≤ 3/20-(a i-1/4) by linarith [hu i])
      nlinarith
    simpa [centeredMoment, mul_sum] using h
  · have h := sum_mul_sq_le_sq_mul_sq univ (fun i => (a i-1/4)^2) (fun _ => (1:ℝ))
    simpa [centeredMoment, ← pow_mul, mul_comm] using h

lemma stability_polynomial {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) :
    (3/100 : ℝ)*centeredMoment a 2 ≤
      (65/24 : ℝ)*moment a 2-(11/3 : ℝ)*moment a 3+
        (10/3 : ℝ)*moment a 4-2*(moment a 2)^2-3/8 := by
  obtain ⟨h0,hQ,hR,hU⟩ := centered_moment_bounds hn hu hs
  obtain ⟨hq,hr,hs'⟩ := centered_moment_identities hs
  rw [hq,hr,hs']
  have hQQ := mul_nonneg h0 (sub_nonneg.mpr hQ)
  nlinarith

end HadwigerRamsey4Col
