import HadwigerRamsey4Col.LiftingFinite
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped BigOperators Classical Topology ENNReal
open Filter Finset Real

namespace HadwigerRamsey4Col.Lifting

/-- The entropy cost with the manuscript's convention `-log 0 = +∞`. -/
noncomputable def extendedCost (p : ℝ) : ℝ≥0∞ :=
  if p = 1 then ⊤ else ENNReal.ofReal (-log (1-p))

/-- The exact ordered entropy sum, with positive masses and extended costs. -/
noncomputable def extendedEnergy {I : Type*} [Fintype I]
    (u : I → ℝ) (p : I → I → ℝ) : ℝ≥0∞ :=
  ∑ i, ∑ j, ENNReal.ofReal (u i * u j) * extendedCost (p i j)

/-- The square root of the extended entropy, including the infinite case. -/
noncomputable def entropyRoot {I : Type*} [Fintype I]
    (u : I → ℝ) (p : I → I → ℝ) : ℝ≥0∞ := extendedEnergy u p ^ (1/2 : ℝ)

lemma finite_positive_lower_bound {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i, δ ≤ f i := by
  classical
  have h (s : Finset I) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i ∈ s, δ ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ,hδ,hδ1,hδs⟩ := ih
      refine ⟨min δ (f a), lt_min hδ (hf a), (min_le_left _ _).trans hδ1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hδs i hi)
  obtain ⟨δ,hδ,hδ1,hδs⟩ := h Finset.univ
  exact ⟨δ,hδ,hδ1,fun i => hδs i (Finset.mem_univ i)⟩

lemma extendedEnergy_eq_capped {I : Type*} [Fintype I]
    (u : I → ℝ) (p : I → I → ℝ) {ζ : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hp : ∀ i j, 0 ≤ p i j)
    (hp1 : ∀ i j, p i j < 1) (hcap : ∀ i j, ζ ≤ 1-p i j) :
    extendedEnergy u p = ENNReal.ofReal (cappedEnergy ζ u p) := by
  have hcost (i j) : cappedCost ζ (p i j) = -log (1-p i j) := by
    rw [cappedCost, min_eq_left (by linarith [hcap i j])]
  have hnonneg (i j) : 0 ≤ u i*u j*(-log (1-p i j)) := by
    apply mul_nonneg (mul_nonneg (hu i) (hu j))
    exact neg_nonneg.mpr (log_nonpos (by linarith [hp1 i j]) (by linarith [hp i j]))
  simp only [extendedEnergy, extendedCost, if_neg (ne_of_lt (hp1 _ _))]
  simp_rw [← ENNReal.ofReal_mul (mul_nonneg (hu _) (hu _))]
  unfold cappedEnergy
  simp_rw [hcost]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hnonneg i j)]

lemma entropyRoot_eq_capped {I : Type*} [Fintype I]
    (u : I → ℝ) (p : I → I → ℝ) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hu : ∀ i, 0 ≤ u i)
    (hp : ∀ i j, 0 ≤ p i j) (hp1 : ∀ i j, p i j < 1)
    (hcap : ∀ i j, ζ ≤ 1-p i j) :
    entropyRoot u p = ENNReal.ofReal (sqrt (cappedEnergy ζ u p)) := by
  rw [entropyRoot, extendedEnergy_eq_capped u p hu hp hp1 hcap,
    ENNReal.ofReal_rpow_of_nonneg (cappedEnergy_nonneg u p hζ hζ1 hu hp) (by norm_num),
    Real.sqrt_eq_rpow]

lemma entropyRoot_eq_top_of_density_one {I : Type*} [Fintype I]
    (u : I → ℝ) (p : I → I → ℝ) (hu : ∀ i, 0 < u i)
    (i j : I) (hp : p i j = 1) : entropyRoot u p = ⊤ := by
  have hterm : ENNReal.ofReal (u i*u j) * extendedCost (p i j) = ⊤ := by
    simp [extendedCost, hp, (ENNReal.ofReal_pos.mpr (mul_pos (hu i) (hu j))).ne']
  have hle : ⊤ ≤ extendedEnergy u p := by
    rw [← hterm]
    unfold extendedEnergy
    calc
      _ ≤ ∑ b, ENNReal.ofReal (u i*u b) * extendedCost (p i b) :=
        Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)
      _ ≤ ∑ a, ∑ b, ENNReal.ofReal (u a*u b) * extendedCost (p a b) :=
        Finset.single_le_sum (f := fun a : I => ∑ b : I, ENNReal.ofReal (u a*u b) * extendedCost (p a b))
          (fun _ _ => bot_le) (Finset.mem_univ i)
  have he : extendedEnergy u p = ⊤ := top_le_iff.mp hle
  simp [entropyRoot, he]

/-- A positive-weight density-one entry makes the capped square-root entropy
unbounded as its cap is removed. -/
theorem cappedEntropy_unbounded {I : Type*} [Fintype I]
    (u : I → ℝ) (p : I → I → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hp : ∀ i j, 0 ≤ p i j) (i j : I) (hui : 0 < u i) (huj : 0 < u j)
    (hpij : p i j = 1) (R : ℝ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧ R < sqrt (cappedEnergy ζ u p) := by
  let M : ℝ := (R^2+1)/(u i*u j)
  have hw : 0 < u i*u j := mul_pos hui huj
  have hM : 0 < M := by dsimp [M]; positivity
  let ζ := exp (-M)
  have hζ : 0 < ζ := exp_pos _
  have hζ1 : ζ < 1 := exp_lt_one_iff.mpr (by linarith)
  have hc : cappedCost ζ (p i j) = M := by
    rw [hpij, cappedCost, min_eq_right (by linarith : 1-ζ ≤ 1)]
    simp only [sub_sub_cancel, log_exp, neg_neg, ζ]
  have ht : u i*u j*cappedCost ζ (p i j) = R^2+1 := by
    rw [hc]
    dsimp [M]
    field_simp
  have hterm (a b : I) : 0 ≤ u a*u b*cappedCost ζ (p a b) :=
    mul_nonneg (mul_nonneg (hu a) (hu b)) (cappedCost_nonneg hζ hζ1.le (hp a b))
  have hbound : R^2+1 ≤ cappedEnergy ζ u p := by
    rw [← ht]
    exact (Finset.single_le_sum (fun b _ => hterm i b) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hterm a b))
        (Finset.mem_univ i))
  refine ⟨ζ,hζ,hζ1,?_⟩
  have hs := Real.sq_sqrt (cappedEnergy_nonneg u p hζ hζ1.le hu hp)
  have hn := Real.sqrt_nonneg (cappedEnergy ζ u p)
  nlinarith

/-- Real eventual lower bounds pass to the extended-real lower limit. -/
lemma ofReal_le_liminf_of_eventually {a : ℕ → ℝ} {b : ℝ}
    (h : ∀ ε > 0, ∀ᶠ n in atTop, b-ε ≤ a n) :
    ENNReal.ofReal b ≤ Filter.liminf (fun n => ENNReal.ofReal (a n)) atTop := by
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (b-1/(m+1 : ℝ))) atTop
      (𝓝 (ENNReal.ofReal b)) := by
    apply (ENNReal.continuous_ofReal.tendsto b).comp
    have ht : Tendsto (fun m : ℕ => (1 : ℝ)/(m+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds.sub ht : Tendsto (fun m : ℕ => b-1/(m+1 : ℝ)) atTop (𝓝 (b-0)))
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro m
  exact le_liminf_of_le (by isBoundedDefault)
    ((h (1/(m+1 : ℝ)) (by positivity)).mono (fun _ hn => ENNReal.ofReal_le_ofReal hn))

/-- Exact passage from all positive entropy caps to the manuscript's full
extended entropy. No strict upper bound on the limiting densities is assumed. -/
theorem entropyRoot_le_liminf {I : Type*} [Fintype I]
    (u : I → ℝ) (p : I → I → ℝ) (hu : ∀ i, 0 < u i)
    (hp : ∀ i j, p i j ∈ Set.Icc (0 : ℝ) 1) (a : ℕ → ℝ)
    (h : ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∀ ε > 0,
      ∀ᶠ n in atTop, sqrt (cappedEnergy ζ u p)-ε ≤ a n) :
    entropyRoot u p ≤ Filter.liminf (fun n => ENNReal.ofReal (a n)) atTop := by
  by_cases hsingular : ∃ i j, p i j = 1
  · obtain ⟨i,j,hij⟩ := hsingular
    rw [entropyRoot_eq_top_of_density_one u p hu i j hij]
    apply top_le_iff.mpr
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro R
    obtain ⟨ζ,hζ,hζ1,hR⟩ := cappedEntropy_unbounded u p (fun i => (hu i).le)
      (fun i j => (hp i j).1) i j (hu i) (hu j) hij R
    have hh := (ENNReal.ofReal_le_ofReal hR.le).trans
      (ofReal_le_liminf_of_eventually (h ζ hζ hζ1))
    simpa using hh
  · have hp1 (i j) : p i j < 1 := lt_of_le_of_ne (hp i j).2
      (fun he => hsingular ⟨i,j,he⟩)
    obtain ⟨δ,hδ,hδ1,hδp⟩ := finite_positive_lower_bound
      (fun q : I × I => 1-p q.1 q.2) (fun q => by linarith [hp1 q.1 q.2])
    let ζ := δ/2
    have hζ : 0 < ζ := by dsimp [ζ]; positivity
    have hζ1 : ζ < 1 := by dsimp [ζ]; linarith
    have hcap (i j) : ζ ≤ 1-p i j := (by dsimp [ζ]; linarith [hδp (i,j)])
    rw [entropyRoot_eq_capped u p hζ hζ1.le (fun i => (hu i).le)
      (fun i j => (hp i j).1) hp1 hcap]
    exact ofReal_le_liminf_of_eventually (h ζ hζ hζ1)

end HadwigerRamsey4Col.Lifting
