import ComponentTransfer.LiftingFinite
import HadwigerRamsey.ThomasonUpper.DensityDeletion

open scoped BigOperators Classical
open Finset Real
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

namespace ComponentTransfer.Lifting

lemma cappedCost_le {ζ p : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hp : 0 ≤ p) :
    cappedCost ζ p ≤ -log ζ :=
  (log_weight_bounds hζ (le_min hp (by linarith)) (min_le_right _ _)).2

/-- Truncation gives a uniform logarithmic Lipschitz bound up to density one. -/
theorem cappedCost_lipschitz {ζ p q : ℝ} (hζ : 0 < ζ) :
    |cappedCost ζ p-cappedCost ζ q| ≤ |p-q|/ζ := by
  have hp : ζ ≤ 1-min p (1-ζ) := by linarith [min_le_right p (1-ζ)]
  have hq : ζ ≤ 1-min q (1-ζ) := by linarith [min_le_right q (1-ζ)]
  have hmin : |min p (1-ζ)-min q (1-ζ)| ≤ |p-q| := by
    have hh := abs_min_sub_min_le_max p (1-ζ) q (1-ζ)
    simp only [sub_self, abs_zero] at hh
    rw [max_eq_left (abs_nonneg (p-q))] at hh
    exact hh
  have h := log_lipschitz hζ hp hq
  dsimp only [cappedCost]
  rw [neg_sub_neg, abs_sub_comm]
  apply h.trans
  apply div_le_div_of_nonneg_right _ hζ.le
  calc
    _ = |min p (1-ζ)-min q (1-ζ)| := by
      rw [show 1-min p (1-ζ)-(1-min q (1-ζ)) = -(min p (1-ζ)-min q (1-ζ)) by ring, abs_neg]
    _ ≤ _ := hmin

lemma partial_mass_product_stability {u v : ℝ} {u' v' d : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hu' : u' ∈ Set.Icc (0 : ℝ) 1) (hv' : v' ∈ Set.Icc (0 : ℝ) 1)
    (hd : 0 ≤ d) (hud : |u-u'| ≤ d) (hvd : |v-v'| ≤ d) :
    |u*v-u'*v'| ≤ 2*d := by
  calc
    _ = |(u-u')*v+u'*(v-v')| := by congr 1; ring
    _ ≤ |u-u'| *v+u'*|v-v'| := by
      simpa only [abs_mul, abs_of_nonneg hv.1, abs_of_nonneg hu'.1]
        using abs_add_le ((u-u')*v) (u'*(v-v'))
    _ ≤ d*v+u'*d := add_le_add
      (mul_le_mul_of_nonneg_right hud hv.1)
      (mul_le_mul_of_nonneg_left hvd hu'.1)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hv.2 hd,
      mul_le_mul_of_nonneg_right hu'.2 hd]

/-- Uniform stability of the capped entropy, including partial probability
vectors. Its constant depends only on the fixed number of selected parts and
on the fixed positive cap. -/
theorem cappedEnergy_stability {I : Type*} [Fintype I]
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (u v : I → ℝ) (p q : I → I → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i j, 0 ≤ p i j) (hq : ∀ i j, 0 ≤ q i j)
    {dm dp : ℝ} (hdm : 0 ≤ dm) (hdp : 0 ≤ dp)
    (hmass : ∀ i, |u i-v i| ≤ dm) (hdensity : ∀ i j, |p i j-q i j| ≤ dp) :
    |cappedEnergy ζ u p-cappedEnergy ζ v q| ≤
      (Fintype.card I : ℝ)^2 * (dp/ζ + 2*dm*(-log ζ)) := by
  have hlog : 0 ≤ -log ζ := neg_nonneg.mpr (log_nonpos hζ.le hζ1)
  have hterm (i j : I) :
      |u i*u j*cappedCost ζ (p i j)-v i*v j*cappedCost ζ (q i j)| ≤
        dp/ζ + 2*dm*(-log ζ) := by
    have hc0 := cappedCost_nonneg hζ hζ1 (hq i j)
    have hcB := cappedCost_le hζ hζ1 (hq i j)
    have huij : u i*u j ≤ 1 := by
      calc
        _ ≤ 1*1 := mul_le_mul (hu i).2 (hu j).2 (hu j).1 (by norm_num)
        _ = 1 := one_mul _
    have hd := (cappedCost_lipschitz (p := p i j) (q := q i j) hζ).trans
      (div_le_div_of_nonneg_right (hdensity i j) hζ.le)
    calc
      _ = |u i*u j*(cappedCost ζ (p i j)-cappedCost ζ (q i j))+
          (u i*u j-v i*v j)*cappedCost ζ (q i j)| := by congr 1; ring
      _ ≤ u i*u j*|cappedCost ζ (p i j)-cappedCost ζ (q i j)|+
          |u i*u j-v i*v j| *cappedCost ζ (q i j) := by
        simpa only [abs_mul, abs_of_nonneg (mul_nonneg (hu i).1 (hu j).1),
          abs_of_nonneg hc0] using abs_add_le
          (u i*u j*(cappedCost ζ (p i j)-cappedCost ζ (q i j)))
          ((u i*u j-v i*v j)*cappedCost ζ (q i j))
      _ ≤ (u i*u j)*(dp/ζ)+(2*dm)*(-log ζ) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hd (mul_nonneg (hu i).1 (hu j).1)
        · exact mul_le_mul
            (partial_mass_product_stability (hu i) (hu j) (hv i) (hv j) hdm
              (hmass i) (hmass j)) hcB hc0 (by positivity)
      _ ≤ _ := by
        apply add_le_add _ le_rfl
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right huij (div_nonneg hdp hζ.le))
  unfold cappedEnergy
  rw [← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ i, ∑ j, |u i*u j*cappedCost ζ (p i j)-v i*v j*cappedCost ζ (q i j)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : I, ∑ _j : I, (dp/ζ+2*dm*(-log ζ)) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
    _ = _ := by simp; ring

/-- An entropy error bounded by a square gives the corresponding additive
square-root error, without a positive lower bound on the entropy. -/
theorem sqrt_le_sqrt_add_of_abs_sub_le_sq {E F ε : ℝ}
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hε : 0 ≤ ε) (herror : |E-F| ≤ ε^2) :
    sqrt E ≤ sqrt F+ε := by
  have hb := (abs_le.mp herror).2
  have hsqE := sq_sqrt hE
  have hsqF := sq_sqrt hF
  have hrootE := sqrt_nonneg E
  have hrootF := sqrt_nonneg F
  nlinarith

end ComponentTransfer.Lifting
