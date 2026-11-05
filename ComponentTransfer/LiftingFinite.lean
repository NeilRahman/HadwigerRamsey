import HadwigerRamsey.Main.Entropy
import HadwigerRamsey.ThomasonUpper.Stability

open scoped BigOperators Classical Topology
open Finset Real Filter
open HadwigerRamsey HadwigerRamsey.ThomasonUpper HadwigerRamsey.Main

namespace ComponentTransfer.Lifting

/-- The bounded entropy cost, retaining the singular value by approximation. -/
noncomputable def cappedCost (ζ p : ℝ) : ℝ := -log (1-min p (1-ζ))

/-- The ordered entropy of a finite collection of possibly partial masses. -/
noncomputable def cappedEnergy {I : Type*} [Fintype I]
    (ζ : ℝ) (u : I → ℝ) (p : I → I → ℝ) : ℝ :=
  ∑ i, ∑ j, u i*u j*cappedCost ζ (p i j)

lemma cappedCost_nonneg {ζ p : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hp : 0 ≤ p) :
    0 ≤ cappedCost ζ p :=
  (log_weight_bounds hζ (le_min hp (by linarith)) (min_le_right _ _)).1

lemma cappedCost_mono_cap {θ ζ p : ℝ} (hθ : 0 < θ) (hθζ : θ ≤ ζ) :
    cappedCost ζ p ≤ cappedCost θ p := by
  apply neg_le_neg
  apply log_le_log
  · have h := min_le_right p (1-θ)
    linarith
  · have h : min p (1-ζ) ≤ min p (1-θ) := min_le_min_left p (by linarith)
    linarith

lemma cappedEnergy_nonneg {I : Type*} [Fintype I] {ζ : ℝ}
    (u : I → ℝ) (p : I → I → ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hu : ∀ i, 0 ≤ u i) (hp : ∀ i j, 0 ≤ p i j) :
    0 ≤ cappedEnergy ζ u p :=
  sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hu i) (hu j)) (cappedCost_nonneg hζ hζ1 (hp i j))

/-- A selected capped entropy matrix is bounded by the whole capped entropy
in the density-sensitive minor theorem. -/
theorem active_capped_energy_le {m k a : ℕ} (H : SimpleGraph (Fin m))
    (σ : Fin m → Fin k) {θ ζ w : ℝ}
    (hθ : 0 < θ) (hθζ : θ ≤ ζ) (hζ1 : ζ ≤ 1) (hw : 0 ≤ w)
    (f : Fin a → Fin k) (hf : Function.Injective f) (u : Fin a → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hmass : ∀ i, w*u i ≤ classMass σ (f i)) :
    w^2*cappedEnergy ζ u (fun i j => blockDensity H σ (f i) (f j)) ≤
      cappedLambda H σ θ := by
  let F := fun i j => classMass σ i * classMass σ j *
    cappedCost θ (blockDensity H σ i j)
  have hθ1 : θ ≤ 1 := hθζ.trans hζ1
  have hF : ∀ i j, 0 ≤ F i j := fun i j =>
    mul_nonneg (mul_nonneg (classMass_nonneg _ _) (classMass_nonneg _ _))
      (cappedCost_nonneg hθ hθ1 (blockDensity_nonneg _ _ _ _))
  have hterm (i j : Fin a) :
      w^2*(u i*u j*cappedCost ζ (blockDensity H σ (f i) (f j))) ≤ F (f i) (f j) := by
    have hh := mul_le_mul (hmass i) (hmass j) (mul_nonneg hw (hu j))
      (classMass_nonneg σ (f i))
    have hc0 := cappedCost_nonneg (hθ.trans_le hθζ) hζ1
      (blockDensity_nonneg H σ (f i) (f j))
    have hc := cappedCost_mono_cap (p := blockDensity H σ (f i) (f j)) hθ hθζ
    have h₁ := mul_le_mul_of_nonneg_right hh hc0
    have h₂ := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (classMass_nonneg σ (f i)) (classMass_nonneg σ (f j)))
    dsimp only [F]
    nlinarith only [h₁,h₂]
  have hfirst : w^2*cappedEnergy ζ u (fun i j => blockDensity H σ (f i) (f j)) ≤
      ∑ i, ∑ j, F (f i) (f j) := by
    unfold cappedEnergy
    simp only [mul_sum]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
  have hsecond : (∑ i, ∑ j, F (f i) (f j)) ≤ ∑ i, ∑ j, F i j := by
    calc
      _ ≤ ∑ i, ∑ j, F (f i) j := sum_le_sum fun i _ =>
        sum_injective_le f hf (F (f i)) (hF (f i))
      _ ≤ _ := sum_injective_le f hf (fun i => ∑ j, F i j)
        (fun i => sum_nonneg fun j _ => hF i j)
  exact hfirst.trans hsecond

/-- Theorem 1.5 on an arbitrary retained graph, normalized by the original
order. Selected masses use that original order, so no logarithmic ratio
limit is needed. -/
theorem normalized_capped_entropy_le {n m k a N : ℕ}
    (H : SimpleGraph (Fin m)) (σ : Fin m → Fin k) {θ ζ K : ℝ}
    (hθ : 0 < θ) (hθζ : θ ≤ ζ) (hζ1 : ζ ≤ 1)
    (hthom : ThomasonBound θ N) (hm2 : 2 ≤ m) (hmn : m ≤ n) (hN : N ≤ m)
    (hconn : θ*m ≤ (vertexConnectivity H : ℝ))
    (hmassall : ∀ j, θ ≤ classMass σ j)
    (f : Fin a → Fin k) (hf : Function.Injective f) (u : Fin a → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hmass : ∀ i, (n : ℝ)/m*u i ≤ classMass σ (f i))
    (hK : (hadwigerNumber H : ℝ) ≤ K) :
    sqrt (cappedEnergy ζ u (fun i j => blockDensity H σ (f i) (f j))) ≤
      K*sqrt (log (n : ℝ))/(n : ℝ)+θ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hK0 : 0 ≤ K := (by positivity : (0 : ℝ) ≤ hadwigerNumber H).trans hK
  have ht := hthom m hN H hconn k σ hmassall
  have hE := active_capped_energy_le H σ hθ hθζ hζ1
    (by positivity : 0 ≤ (n : ℝ)/m) f hf u hu hmass
  have hroot : (n : ℝ)/m * sqrt (cappedEnergy ζ u (fun i j => blockDensity H σ (f i) (f j))) ≤
      sqrt (cappedLambda H σ θ) := by
    have hh := sqrt_le_sqrt hE
    rw [sqrt_mul (sq_nonneg _),sqrt_sq_eq_abs,
      abs_of_nonneg (show 0 ≤ (n : ℝ)/m by positivity)] at hh
    exact hh
  have hrootm : 0 < sqrt (log (m : ℝ)) :=
    sqrt_pos.mpr (log_pos (by exact_mod_cast (by omega : 1 < m)))
  have hroots : sqrt (log (m : ℝ)) ≤ sqrt (log (n : ℝ)) :=
    sqrt_le_sqrt (log_le_log hmR (by exact_mod_cast hmn))
  have ht' : sqrt (cappedLambda H σ θ)-θ ≤ K*sqrt (log (m : ℝ))/m := by
    have hh := ht.trans hK
    have hpos : 0 < (m : ℝ)/sqrt (log (m : ℝ)) := div_pos hmR hrootm
    have hh' : (sqrt (cappedLambda H σ θ)-θ)*((m : ℝ)/sqrt (log (m : ℝ))) ≤ K := by
      nlinarith only [hh]
    have hd := (le_div_iff₀ hpos).mpr hh'
    convert hd using 1 <;> first | rfl | field_simp
  have hbound : (n : ℝ)/m * sqrt (cappedEnergy ζ u (fun i j => blockDensity H σ (f i) (f j))) ≤
      K*sqrt (log (m : ℝ))/m+θ := by linarith only [hroot,ht']
  have hmult := mul_le_mul_of_nonneg_right hbound hmR.le
  have he : ((n : ℝ)/m*sqrt (cappedEnergy ζ u (fun i j => blockDensity H σ (f i) (f j))))*(m : ℝ) =
      (n : ℝ)*sqrt (cappedEnergy ζ u (fun i j => blockDensity H σ (f i) (f j))) := by field_simp
  have he' : (K*sqrt (log (m : ℝ))/m+θ)*(m : ℝ) = K*sqrt (log (m : ℝ))+θ*m := by field_simp
  rw [he,he'] at hmult
  have hhP := mul_le_mul_of_nonneg_left (show (m : ℝ) ≤ n by exact_mod_cast hmn) hθ.le
  have hhroot := mul_le_mul_of_nonneg_left hroots hK0
  have hd := div_mul_cancel₀ (K*sqrt (log (n : ℝ))) hnR.ne'
  by_contra! hbad
  have hbad' := mul_lt_mul_of_pos_right hbad hnR
  nlinarith only [hmult,hhP,hhroot,hd,hbad']

end ComponentTransfer.Lifting
