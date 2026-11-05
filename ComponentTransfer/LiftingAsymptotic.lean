import ComponentTransfer.LiftingDeletion
import ComponentTransfer.TransferCore

open scoped BigOperators Classical Topology
open Finset Real Filter
open HadwigerRamsey HadwigerRamsey.ThomasonUpper HadwigerRamsey.Main
open HadwigerRamsey.ControlledPartition

set_option maxHeartbeats 1800000

namespace ComponentTransfer.Lifting

/-- The finite entropy lower bound passes to limits as soon as every balanced
cut has a positive quadratic lower bound. This isolates the purely finite
part of entropy lifting from the connected graphon expansion theorem. -/
theorem capped_lower_of_balanced_cuts {k l : ℕ}
    (N M : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hM : Tendsto M atTop atTop)
    (hMN : ∀ᶠ n in atTop, M n ≤ N n)
    (G : ∀ n, SimpleGraph (Fin (M n))) (τ : ∀ n, Fin (M n) → Fin l)
    (K : ℕ → ℝ) (hK : ∀ n, (hadwigerNumber (G n) : ℝ) ≤ K n)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hclasses : ∀ᶠ n in atTop, ∀ i, a ≤ classMass (τ n) i)
    (f : Fin k → Fin l) (hf : Function.Injective f)
    (lam : Fin k → ℝ) (p : Fin k → Fin k → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (hp : ∀ i j, 0 ≤ p i j)
    (hmass : ∀ i, Tendsto (fun n => ((classVertices (τ n) (f i)).card : ℝ)/(N n : ℝ))
      atTop (𝓝 (lam i)))
    (hdensity : ∀ i j, Tendsto (fun n => blockDensity (G n) (τ n) (f i) (f j))
      atTop (𝓝 (p i j)))
    (hcut : ∀ ρ : ℝ, 0 < ρ → ρ < 1/4 → ∃ σ : ℝ, 0 < σ ∧
      ∀ᶠ n in atTop, ∀ A : Finset (Fin (M n)),
        ρ*M n ≤ (A.card : ℝ) → (A.card : ℝ) ≤ (1-ρ)*M n →
        σ*(M n : ℝ)^2 ≤ ((G n).interedges A (univ \ A)).card)
    {ζ ε : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 < ε) :
    ∀ᶠ n in atTop, sqrt (cappedEnergy ζ lam p)-ε ≤ K n*sqrt (log (N n : ℝ))/(N n : ℝ) := by
  let e := ε/4
  have he : 0 < e := by dsimp [e]; positivity
  have hlog : 0 ≤ -log ζ := neg_nonneg.mpr (log_nonpos hζ.le hζ1)
  let D : ℝ := (k : ℝ)^2*((8/a+1)/ζ+4*(-log ζ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let ρ := min (1/8 : ℝ) (min (a/4) (e^2/(D+1)))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ8 : ρ ≤ 1/8 := min_le_left _ _
  have hρa : ρ < a/2 := by
    have hh : ρ ≤ a/4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hρD : D*ρ ≤ e^2 := by
    have hh : ρ ≤ e^2/(D+1) := (min_le_right _ _).trans (min_le_right _ _)
    have ht := (le_div_iff₀ (show 0 < D+1 by positivity)).mp hh
    nlinarith [hρ]
  obtain ⟨σ, hσ, hcuts⟩ := hcut ρ hρ (by linarith)
  let θ := min ζ (min (a/4) (min (σ/4) e))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθζ : θ ≤ ζ := min_le_left _ _
  have hθa : θ ≤ a/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hθσ : θ ≤ σ/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθe : θ ≤ e := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨T, hthom⟩ := exists_thomason_bound hθ
  have hMr : Tendsto (fun n => (M n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
  have hNpos := hN.eventually_gt_atTop 0
  have hMsize := hMr.eventually_ge_atTop (4/a)
  have hMσ := hMr.eventually_ge_atTop (4/σ)
  have hMT := hMr.eventually_ge_atTop (2*(T : ℝ)+4)
  have hmassclose : ∀ᶠ n in atTop, ∀ i,
      |((classVertices (τ n) (f i)).card : ℝ)/(N n : ℝ)-lam i| ≤ ρ := by
    rw [Filter.eventually_all]
    intro i
    have hh := (hmass i).sub_const (lam i)
    have hh' := hh.abs
    have hh'' := (tendsto_order.mp hh').2 ρ (by simpa only [sub_self, abs_zero] using hρ)
    simpa only [sub_self, abs_zero] using hh''.mono (fun n hn => hn.le)
  have hdensityclose : ∀ᶠ n in atTop, ∀ i j,
      |blockDensity (G n) (τ n) (f i) (f j)-p i j| ≤ ρ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hh := ((hdensity i j).sub_const (p i j)).abs
    have hh' := (tendsto_order.mp hh).2 ρ (by simpa only [sub_self, abs_zero] using hρ)
    simpa only [sub_self, abs_zero] using hh'.mono (fun n hn => hn.le)
  filter_upwards [hMN,hNpos,hMsize,hMσ,hMT,hclasses,hcuts,hmassclose,hdensityclose]
    with n hmn hn hmsize hmσ hmT hclass hcuts hmassclose hdensityclose
  have hmR : (0 : ℝ) < M n := by nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have hm2 : 2 ≤ M n := by exact_mod_cast (show (2 : ℝ) ≤ M n by nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have hm4 : 4 ≤ a*M n := by simpa only [mul_comm] using (div_le_iff₀ ha).mp hmsize
  have hmσ4 : 4 ≤ σ*M n := by simpa only [mul_comm] using (div_le_iff₀ hσ).mp hmσ
  have hsize (i : Fin l) : a*M n ≤ ((classVertices (τ n) i).card : ℝ) := by
    have hh := hclass i
    change a ≤ ((classVertices (τ n) i).card : ℝ)/(M n : ℝ) at hh
    exact (le_div_iff₀ hmR).mp hh
  obtain ⟨P,hP,hconn⟩ := connected_core (G n) hm2 hρ (by linarith) hσ hcuts
  have hPM : P.card ≤ M n := by simpa using P.card_le_univ
  have hPMR : (P.card : ℝ) ≤ M n := by exact_mod_cast hPM
  have hρM : ρ*(M n : ℝ) ≤ (M n : ℝ)/8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hρ8 hmR.le]
  have hP2 : 2 ≤ P.card := by
    exact_mod_cast (show (2 : ℝ) ≤ P.card by nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have hPT : T ≤ P.card := by
    exact_mod_cast (show (T : ℝ) ≤ P.card by nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have hPdel : ((univ \ P).card : ℝ) ≤ ρ*M n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hPM]
    linarith
  have hb := retained_partition_bounds (G n) (τ n) P ha ha1 hρ.le hρa hm4 hPdel hsize
  have hconnR : θ*P.card ≤ (vertexConnectivity (inducedGraph (G n) P) : ℝ) := by
    have hfloor := Nat.sub_one_lt_floor (σ*(M n : ℝ)/2)
    have hc : (⌊σ*(M n : ℝ)/2⌋₊ : ℝ) ≤ vertexConnectivity (inducedGraph (G n) P) := by exact_mod_cast hconn
    nlinarith [mul_le_mul_of_nonneg_left hPMR hθ.le,
      mul_le_mul_of_nonneg_right hθσ hmR.le]
  let u : Fin k → ℝ := fun i => retainedMass (N n) (τ n) P (f i)
  let q : Fin k → Fin k → ℝ := fun i j =>
    blockDensity (inducedGraph (G n) P) (retainedClasses (τ n) P) (f i) (f j)
  have hu (i) : u i ∈ Set.Icc (0 : ℝ) 1 := retainedMass_bounds hmn (τ n) P (f i)
  have hq (i j) : 0 ≤ q i j := blockDensity_nonneg _ _ _ _
  have hmasserror (i) : |lam i-u i| ≤ 2*ρ := by
    have hh := retainedMass_error hn hmn (τ n) P hρ.le hPdel (f i)
    have ht := abs_sub_le (u i) (((classVertices (τ n) (f i)).card : ℝ)/(N n : ℝ)) (lam i)
    rw [abs_sub_comm (lam i)]
    linarith [hmassclose i]
  have hdensityerror (i j) : |p i j-q i j| ≤ 8*ρ/a+ρ := by
    have ht := abs_sub_le (q i j) (blockDensity (G n) (τ n) (f i) (f j)) (p i j)
    rw [abs_sub_comm (p i j)]
    have hh := hb.2 (f i) (f j)
    change |q i j-blockDensity (G n) (τ n) (f i) (f j)| ≤ 8*ρ/a at hh
    linarith [hdensityclose i j]
  have hE := cappedEnergy_stability ζ hζ hζ1 lam u p q hlam hu hp hq
    (by positivity : 0 ≤ 2*ρ) (by positivity : 0 ≤ 8*ρ/a+ρ) hmasserror hdensityerror
  have herr : |cappedEnergy ζ lam p-cappedEnergy ζ u q| ≤ e^2 := by
    apply hE.trans
    have heq : (Fintype.card (Fin k) : ℝ)^2*((8*ρ/a+ρ)/ζ+2*(2*ρ)*(-log ζ)) = D*ρ := by
      simp only [Fintype.card_fin]
      dsimp only [D]
      ring
    rwa [heq]
  have hsqrt := sqrt_le_sqrt_add_of_abs_sub_le_sq
    (cappedEnergy_nonneg lam p hζ hζ1 (fun i => (hlam i).1) hp)
    (cappedEnergy_nonneg u q hζ hζ1 (fun i => (hu i).1) hq) he.le herr
  have hminor : (hadwigerNumber (inducedGraph (G n) P) : ℝ) ≤ K n := by
    have hh : (hadwigerNumber (inducedGraph (G n) P) : ℝ) ≤ hadwigerNumber (G n) := by
      exact_mod_cast inducedGraph_hadwiger_le (G n) P
    exact hh.trans (hK n)
  have hfinite := normalized_capped_entropy_le (inducedGraph (G n) P)
    (retainedClasses (τ n) P) hθ hθζ hζ1 hthom hP2 (hPM.trans hmn) hPT hconnR
    (fun i => (show θ ≤ a/2 by linarith).trans (hb.1 i)) f hf u
    (fun i => (hu i).1) (fun i => (retainedMass_scale hn (τ n) P (f i)).le) hminor
  change sqrt (cappedEnergy ζ u q) ≤ _ at hfinite
  dsimp only [e] at hθe hsqrt
  linarith

end ComponentTransfer.Lifting
