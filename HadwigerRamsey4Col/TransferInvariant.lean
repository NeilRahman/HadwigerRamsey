import HadwigerRamsey4Col.LiftingLemma
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open scoped Classical Topology ENNReal symmDiff
open MeasureTheory Filter Set

namespace HadwigerRamsey4Col.Transfer

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- A measurable invariant set: almost every positive kernel edge preserves
membership in the set. -/
def Invariant (W : Graphon α μ) (S : Set α) : Prop :=
  MeasurableSet S ∧ ∀ᵐ p ∂μ.prod μ, W.toAEEqFun p ≠ 0 → (p.1 ∈ S ↔ p.2 ∈ S)

lemma invariant_empty (W : Graphon α μ) : Invariant W ∅ :=
  ⟨MeasurableSet.empty, Eventually.of_forall (by simp)⟩

lemma Invariant.compl {W : Graphon α μ} {S : Set α} (h : Invariant W S) : Invariant W Sᶜ := by
  refine ⟨h.1.compl, ?_⟩
  filter_upwards [h.2] with p hp
  exact fun hn => not_congr (hp hn)

lemma Invariant.inter {W : Graphon α μ} {S T : Set α}
    (hS : Invariant W S) (hT : Invariant W T) : Invariant W (S ∩ T) := by
  refine ⟨hS.1.inter hT.1, ?_⟩
  filter_upwards [hS.2,hT.2] with p hS hT
  exact fun hn => and_congr (hS hn) (hT hn)

lemma Invariant.sdiff {W : Graphon α μ} {S T : Set α}
    (hS : Invariant W S) (hT : Invariant W T) : Invariant W (S \ T) :=
  hS.inter hT.compl

lemma Invariant.rectIntegral_zero {W : Graphon α μ} {S : Set α} (h : Invariant W S) :
    W.toSymmKernel.rectIntegral S Sᶜ = 0 := by
  apply setIntegral_eq_zero_of_ae_eq_zero
  filter_upwards [h.2] with p hp hmem
  by_contra hn
  exact hmem.2 ((hp hn).mp hmem.1)

lemma invariant_of_rectIntegral_zero (W : Graphon α μ) (S : Set α)
    (hS : MeasurableSet S) (hz : W.toSymmKernel.rectIntegral S Sᶜ = 0) : Invariant W S := by
  have hn : ∀ᵐ p ∂(μ.prod μ).restrict (S ×ˢ Sᶜ), 0 ≤ W.toAEEqFun p :=
    (ae_restrict_of_ae W.ae_mem_Icc).mono (fun _ hp => hp.1)
  have heq : W.toAEEqFun =ᵐ[(μ.prod μ).restrict (S ×ˢ Sᶜ)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hn (SymmKernel.graphon_integrable W).integrableOn).mp hz
  have hforward : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S → p.2 ∉ S → W.toAEEqFun p = 0 := by
    change (∀ᵐ p ∂(μ.prod μ).restrict (S ×ˢ Sᶜ), W.toAEEqFun p = 0) at heq
    rw [ae_restrict_iff' (hS.prod hS.compl)] at heq
    filter_upwards [heq] with p hp h₁ h₂
    exact hp ⟨h₁,h₂⟩
  have hback := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hforward
  refine ⟨hS, ?_⟩
  filter_upwards [hforward,hback,W.symm_ae] with p hf hb hs
  intro hn
  constructor
  · intro h₁
    by_contra h₂
    exact hn (hf h₁ h₂)
  · intro h₂
    by_contra h₁
    exact hn (hs.symm.trans (hb h₂ h₁))

noncomputable def invariantIndicator (W : Graphon α μ) (S : {S : Set α // Invariant W S}) :
    Lp ℝ 1 μ := indicatorConstLp 1 S.property.1 (measure_ne_top μ S) 1

lemma invariantIndicator_dist (W : Graphon α μ) (S T : {S : Set α // Invariant W S}) :
    dist (invariantIndicator W S) (invariantIndicator W T) = μ.real (S.val ∆ T.val) := by
  rw [invariantIndicator,invariantIndicator,dist_indicatorConstLp_eq_norm,
    norm_indicatorConstLp (by norm_num) (by norm_num)]
  norm_num

/-- A separable measure has a countable family approximating every invariant
set in symmetric-difference measure. -/
theorem exists_dense_invariant_sequence (W : Graphon α μ) [IsSeparable μ] :
    ∃ S : ℕ → Set α, (∀ n, Invariant W (S n)) ∧
      ∀ T : Set α, Invariant W T → ∀ ε > 0, ∃ n, μ.real (T ∆ S n) < ε := by
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  let Z := Set.range (invariantIndicator W)
  have : Nonempty Z := ⟨⟨invariantIndicator W ⟨∅,invariant_empty W⟩,⟨⟨∅,invariant_empty W⟩,rfl⟩⟩⟩
  obtain ⟨d,hd⟩ := TopologicalSpace.exists_dense_seq Z
  have hpre (n : ℕ) : ∃ s : {S : Set α // Invariant W S}, invariantIndicator W s = (d n).val :=
    (d n).property
  choose s hs using hpre
  refine ⟨fun n => (s n).val,fun n => (s n).property,?_⟩
  intro T hT ε hε
  obtain ⟨n,hn⟩ := hd.exists_dist_lt ⟨invariantIndicator W ⟨T,hT⟩,⟨⟨T,hT⟩,rfl⟩⟩ hε
  have hdist : dist (invariantIndicator W ⟨T,hT⟩) ((d n).val) < ε := hn
  rw [← hs n,invariantIndicator_dist] at hdist
  exact ⟨n,hdist⟩

end HadwigerRamsey4Col.Transfer
