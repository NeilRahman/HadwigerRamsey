import HadwigerRamsey4Col.LiftingAsymptotic
import HadwigerRamsey4Col.LiftingEntropy
import HadwigerRamsey4Col.LiftingPartitionData
import HadwigerRamsey4Col.LiftingCutTransfer
import HadwigerRamsey4Col.LiftingExpansionAtomless

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Finset Real
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

namespace HadwigerRamsey4Col.Lifting

lemma cond_probability_of_real_pos {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Set α) (hpos : 0 < μ.real S) :
    IsProbabilityMeasure (cond μ S) := by
  apply cond_isProbabilityMeasure
  intro hz
  have hh : μ.real S = 0 := by simp [measureReal_def, hz]
  linarith

/-- The analytic and finite parts of entropy lifting, for the realized
partition of a region whose finite graphs satisfy every balanced cut bound. -/
theorem entropy_lower_of_realized_balanced_cuts
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {r k : ℕ} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (c : Fin r) (S : Set α) (hSpos : 0 < μ.real S) (A : Fin k → Set α)
    (hpos : ∀ i, 0 < μ.real (A i)) [IsProbabilityMeasure (cond μ S)]
    (D : Realization.LiftingPartitionData μ N G W S A)
    (hcut : ∀ ρ : ℝ, 0 < ρ → ρ < 1/4 → ∃ σ : ℝ, 0 < σ ∧
      ∀ᶠ n in atTop, ∀ B : Finset (Fin (D.region n).card),
        ρ*(D.region n).card ≤ (B.card : ℝ) →
        (B.card : ℝ) ≤ (1-ρ)*(D.region n).card →
        σ*((D.region n).card : ℝ)^2 ≤
          ((Realization.selectedGraph (G n c) (D.region n)).interedges B (univ \ B)).card) :
    entropyRoot (fun i => μ.real (A i))
      (fun i j => (W c).toSymmKernel.rectIntegral (A i) (A j) /
        (μ.real (A i)*μ.real (A j))) ≤
      Filter.liminf (fun n => ENNReal.ofReal
        ((hadwigerNumber (G n c) : ℝ)*sqrt (log (N n : ℝ))/(N n : ℝ))) atTop := by
  obtain ⟨b,hb,hb1,hbm⟩ := finite_positive_lower_bound D.masses D.masses_pos
  let a := b/2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hclasses : ∀ᶠ n in atTop, ∀ j, a ≤ classMass (D.labels n) j := by
    rw [Filter.eventually_all]
    intro j
    have haj : a < D.masses j := by dsimp [a]; linarith [hbm j]
    exact ((tendsto_order.mp (D.masses_tendsto j)).1 a haj).mono fun n hn => hn.le
  apply entropyRoot_le_liminf (fun i => μ.real (A i))
    (fun i j => (W c).toSymmKernel.rectIntegral (A i) (A j) /
      (μ.real (A i)*μ.real (A j))) hpos (D.density_mem_Icc c)
  intro ζ hζ hζ1 ε hε
  have hminor (n : ℕ) :
      (hadwigerNumber (Realization.selectedGraph (G n c) (D.region n)) : ℝ) ≤
        hadwigerNumber (G n c) := by
    exact_mod_cast hadwigerNumber_comap_le (G n c) (Realization.selectedEmbedding (D.region n))
      (Realization.selectedEmbedding (D.region n)).injective
  exact capped_lower_of_balanced_cuts N (fun n => (D.region n).card) hN D.region_order
    (Eventually.of_forall fun n => by simpa using (D.region n).card_le_univ)
    (fun n => Realization.selectedGraph (G n c) (D.region n)) D.labels
    (fun n => (hadwigerNumber (G n c) : ℝ)) hminor a ha ha1 hclasses
    D.active D.active.injective (fun i => μ.real (A i))
    (fun i j => (W c).toSymmKernel.rectIntegral (A i) (A j) /
      (μ.real (A i)*μ.real (A j)))
    (fun i => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (fun i j => (D.density_mem_Icc c i j).1)
    (D.active_global_mass_tendsto hN hSpos) (D.density_tendsto c) hcut hζ hζ1.le hε

end HadwigerRamsey4Col.Lifting

namespace HadwigerRamsey4Col

open Lifting Realization
open scoped unitInterval

/-- **Lemma 8 of `comptransfer.tex`.** A connected positive-measure graphon
restriction lifts every finite entropy matrix of disjoint positive subsets
to a lower bound for the normalized Hadwiger numbers. The entropy and lower
limit take values in the extended nonnegative reals, so a density equal to
one has exactly the manuscript's infinite logarithmic cost.

Connected components satisfy the connected-restriction hypothesis. The proof
uses no hypothesis about edges outside the region and therefore also proves
this stronger connected-restriction form. -/
theorem lemma8 {r k : ℕ} (hr : 2 ≤ r)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → GraphonI)
    (hconv : FiniteGraphCommonCutConverges (volume : Measure I) N G W)
    (c : Fin r) (S : Set I) (hS : MeasurableSet S) (hSpos : 0 < (volume : Measure I).real S)
    (hconnected :
      letI := cond_probability_of_real_pos (volume : Measure I) S hSpos
      Connected (restrictGraphon (W c) S))
    (A : Fin k → Set I) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hsub : ∀ i, A i ⊆ S) (hpos : ∀ i, 0 < (volume : Measure I).real (A i)) :
    entropyRoot (fun i => (volume : Measure I).real (A i))
      (fun i j => (W c).toSymmKernel.rectIntegral (A i) (A j) /
        ((volume : Measure I).real (A i)*(volume : Measure I).real (A j))) ≤
      Filter.liminf (fun n => ENNReal.ofReal
        ((hadwigerNumber (G n c) : ℝ)*sqrt (log (N n : ℝ))/(N n : ℝ))) atTop := by
  by_cases hk : 0 < k
  · letI := cond_probability_of_real_pos (volume : Measure I) S hSpos
    letI : NullSingletonClass (cond (volume : Measure I) S) := cond_nullSingletonClass S
    have htotal := Connected.integral_pos_unitInterval (restrictGraphon (W c) S) hconnected
    obtain ⟨D⟩ := exists_lifting_partition_data (volume : Measure I) hr hk N hN G W hconv
      S hS hSpos A hA hdisjoint hsub hpos
    apply entropy_lower_of_realized_balanced_cuts hN G W c S hSpos A hpos D
    intro ρ hρ hρ4
    exact finite_balanced_cuts_of_common_cut (cond (volume : Measure I) S)
      (fun n => (D.region n).card)
      (fun n c => selectedGraph (G n c) (D.region n))
      (fun c => restrictGraphon (W c) S) D.region_converges c hconnected htotal ρ hρ hρ4
  · have hk0 : k = 0 := by omega
    subst k
    have hzero : entropyRoot (fun i : Fin 0 => (volume : Measure I).real (A i))
        (fun i j => (W c).toSymmKernel.rectIntegral (A i) (A j) /
          ((volume : Measure I).real (A i)*(volume : Measure I).real (A j))) = 0 := by
      simp [entropyRoot, extendedEnergy]
    rw [hzero]
    exact bot_le

end HadwigerRamsey4Col
