/-
The Radon--Nikodym rectangle calculation adapts Graphon.CutNormPullback,
Copyright (c) 2026 Cameron Freer. Released under the Apache 2.0 license;
see vendor/graphon/LICENSE and vendor/graphon/README.md.
-/
import ComponentTransfer.LiftingExpansionPositive
import ComponentTransfer.LiftingExpansionUniform
import ComponentTransfer.RealizationCouplingInput
import ComponentTransfer.LiftingFiniteCut

open scoped Classical Topology ENNReal
open MeasureTheory Filter Set
open ComponentTransfer.Realization

namespace ComponentTransfer.Lifting

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {μ : Measure α} {ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The image of a restricted probability measure is a submeasure of the
image probability measure. -/
lemma map_restrict_le_of_measurePreserving (φ : Ω → α) (hφ : MeasurePreserving φ ν μ)
    (A : Set Ω) : (ν.restrict A).map φ ≤ μ := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply hφ.measurable hB, Measure.restrict_apply (hφ.measurable hB)]
  exact (measure_mono Set.inter_subset_left).trans_eq (hφ.measure_preimage hB.nullMeasurableSet)

/-- A source cut in any probability coupling has an actual fractional
profile on the target. Both its mass and its graphon boundary are preserved. -/
theorem exists_fractional_cut_profile (W : Graphon α μ)
    (φ : Ω → α) (hφ : MeasurePreserving φ ν μ) (A : Set Ω) (hA : MeasurableSet A) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∫ x, f x ∂μ) = ν.real A ∧
      fractionalCut W f =
        (Graphon.pullback W φ hφ).toSymmKernel.rectIntegral A Aᶜ := by
  let νA := (ν.restrict A).map φ
  let νB := (ν.restrict Aᶜ).map φ
  have hleA : νA ≤ μ := map_restrict_le_of_measurePreserving φ hφ A
  have hleB : νB ≤ μ := map_restrict_le_of_measurePreserving φ hφ Aᶜ
  have hacA : νA ≪ μ := Measure.absolutelyContinuous_of_le hleA
  have hacB : νB ≪ μ := Measure.absolutelyContinuous_of_le hleB
  letI : IsFiniteMeasure νA := ⟨lt_of_le_of_lt (hleA univ) (measure_lt_top μ _)⟩
  letI : IsFiniteMeasure νB := ⟨lt_of_le_of_lt (hleB univ) (measure_lt_top μ _)⟩
  let f₀ : α → ℝ := fun x => (νA.rnDeriv μ x).toReal
  let g₀ : α → ℝ := fun x => (νB.rnDeriv μ x).toReal
  have hf₀ : Measurable f₀ := (Measure.measurable_rnDeriv νA μ).ennreal_toReal
  have hg₀ : Measurable g₀ := (Measure.measurable_rnDeriv νB μ).ennreal_toReal
  have hf₀le : ∀ᵐ x ∂μ, f₀ x ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hleA] with x hx
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hx).trans_eq ENNReal.toReal_one
  let f : α → ℝ := fun x => min (f₀ x) 1
  have hf : Measurable f := hf₀.min measurable_const
  have hfbound (x : α) : f x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min ENNReal.toReal_nonneg zero_le_one,min_le_right _ _⟩
  have hfeq : f =ᵐ[μ] f₀ := hf₀le.mono (fun x hx => min_eq_left hx)
  have hsum : νA+νB = μ := by
    rw [← Measure.map_add _ _ hφ.measurable, Measure.restrict_add_restrict_compl hA, hφ.map_eq]
  have hgrel : g₀ =ᵐ[μ] fun x => 1-f x := by
    have hadd := Measure.rnDeriv_add' νA νB μ
    rw [hsum] at hadd
    filter_upwards [hadd, μ.rnDeriv_self, Measure.rnDeriv_lt_top νA μ,
      Measure.rnDeriv_lt_top νB μ, hfeq] with x hx hs ha hb hf
    have hh := congrArg ENNReal.toReal (hx.symm.trans hs)
    simp only [Pi.add_apply] at hh
    rw [ENNReal.toReal_add ha.ne hb.ne, ENNReal.toReal_one] at hh
    dsimp only [g₀,f₀] at *
    linarith
  have hmass : (∫ x, f x ∂μ) = ν.real A := by
    rw [integral_congr_ae hfeq, Measure.integral_toReal_rnDeriv hacA]
    simp only [measureReal_def, νA]
    rw [Measure.map_apply hφ.measurable MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
  have hmap : Measure.map (Prod.map φ φ) ((ν.prod ν).restrict (A ×ˢ Aᶜ)) = νA.prod νB := by
    rw [← Measure.prod_restrict, ← Measure.map_prod_map _ _ hφ.measurable hφ.measurable]
  have heq : ∫ p in A ×ˢ Aᶜ, W.toAEEqFun (φ p.1,φ p.2) ∂ν.prod ν =
      ∫ p, f₀ p.1*g₀ p.2*W.toAEEqFun p ∂μ.prod μ := by
    calc
      _ = ∫ p, W.toAEEqFun (Prod.map φ φ p) ∂(ν.prod ν).restrict (A ×ˢ Aᶜ) := rfl
      _ = ∫ p, W.toAEEqFun p ∂Measure.map (Prod.map φ φ) ((ν.prod ν).restrict (A ×ˢ Aᶜ)) :=
        (integral_map (hφ.measurable.prodMap hφ.measurable).aemeasurable
          W.toAEEqFun.stronglyMeasurable.aestronglyMeasurable).symm
      _ = ∫ p, W.toAEEqFun p ∂νA.prod νB := by rw [hmap]
      _ = ∫ p, W.toAEEqFun p ∂(μ.prod μ).withDensity
          (fun p => νA.rnDeriv μ p.1*νB.rnDeriv μ p.2) := by
        rw [← MeasureTheory.prod_withDensity (Measure.measurable_rnDeriv νA μ)
          (Measure.measurable_rnDeriv νB μ),
          Measure.withDensity_rnDeriv_eq νA μ hacA, Measure.withDensity_rnDeriv_eq νB μ hacB]
      _ = ∫ p, (νA.rnDeriv μ p.1*νB.rnDeriv μ p.2).toReal • W.toAEEqFun p ∂μ.prod μ := by
        apply integral_withDensity_eq_integral_toReal_smul
        · exact ((Measure.measurable_rnDeriv νA μ).comp measurable_fst).mul
            ((Measure.measurable_rnDeriv νB μ).comp measurable_snd)
        · filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.rnDeriv_lt_top νA μ),
            Measure.quasiMeasurePreserving_snd.ae (Measure.rnDeriv_lt_top νB μ)] with p ha hb
          exact ENNReal.mul_lt_top ha hb
      _ = _ := by
        congr 1
        funext p
        rw [smul_eq_mul, ENNReal.toReal_mul]
  refine ⟨f,hf,hfbound,hmass,?_⟩
  unfold SymmKernel.rectIntegral
  rw [show (∫ p in A ×ˢ Aᶜ, (Graphon.pullback W φ hφ).toAEEqFun p ∂ν.prod ν) =
      ∫ p in A ×ˢ Aᶜ, W.toAEEqFun (φ p.1,φ p.2) ∂ν.prod ν from
    integral_congr_ae (ae_restrict_of_ae (Graphon.pullback_ae W φ hφ))]
  rw [heq]
  unfold fractionalCut
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfeq,
    Measure.quasiMeasurePreserving_snd.ae hgrel] with p hx hy
  rw [hx,hy]
  ring

/-- Small cut error transfers the target's uniform fractional expansion to
an arbitrary measurable cut in a common alignment space. -/
theorem aligned_cut_lower (U : Graphon Ω ν) (W : Graphon α μ)
    (φ : Ω → α) (hφ : MeasurePreserving φ ν μ) {ρ σ ε : ℝ}
    (hbound : ∀ f : α → ℝ, Measurable f →
      (∀ᵐ x ∂μ, f x ∈ Icc (0 : ℝ) 1) →
      (∫ x, f x ∂μ) ∈ Icc ρ (1-ρ) → σ ≤ fractionalCut W f)
    (hcost : Graphon.cutNormDiff U (Graphon.pullback W φ hφ) ≤ ε)
    (A : Set Ω) (hA : MeasurableSet A) (hmass : ν.real A ∈ Icc ρ (1-ρ)) :
    σ-ε ≤ U.toSymmKernel.rectIntegral A Aᶜ := by
  obtain ⟨f,hf,hfb,hm,hboundary⟩ := exists_fractional_cut_profile W φ hφ A hA
  have hb := hbound f hf (Eventually.of_forall hfb) (by simpa only [hm] using hmass)
  rw [hboundary] at hb
  have hc := Graphon.abs_rectIntegralDiff_le U (Graphon.pullback W φ hφ) hA hA.compl
  rw [Graphon.rectIntegralDiff_eq] at hc
  have hd := (abs_le.mp (hc.trans hcost)).1
  linarith

/-- Common coloured cut convergence to a connected graphon forces uniform
quadratic edge expansion of every balanced cut in the corresponding colour. -/
theorem finite_balanced_cuts_of_common_cut
    (μ : Measure α) [IsProbabilityMeasure μ] {r : ℕ}
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (W : Fin r → Graphon α μ) (hconv : FiniteGraphCommonCutConverges μ N G W)
    (c : Fin r) (hW : Connected (W c))
    (htotal : 0 < ∫ p, (W c).toAEEqFun p ∂μ.prod μ)
    (ρ : ℝ) (hρ : 0 < ρ) (_hρ4 : ρ < 1/4) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ n in atTop, ∀ A : Finset (Fin (N n)),
      ρ*(N n : ℝ) ≤ A.card → (A.card : ℝ) ≤ (1-ρ)*N n →
      σ*(N n : ℝ)^2 ≤ ((G n c).interedges A (Finset.univ \ A)).card := by
  obtain ⟨σ,hσ,hbound⟩ := exists_uniform_fractionalCut_bound μ (W c) hW htotal hρ
  refine ⟨σ/2,by positivity,?_⟩
  filter_upwards [hconv (σ/2) (by positivity)] with n hn
  obtain ⟨hne,π,hπ⟩ := hn
  letI : Nonempty (Fin (N n)) := hne
  letI : IsProbabilityMeasure π.law := π.probability
  have hnR : (0 : ℝ) < N n := by
    exact_mod_cast (show 0 < N n by simpa using (Fintype.card_pos (α := Fin (N n))))
  intro A hAlow hAhigh
  have hA : MeasurableSet (A : Set (Fin (N n))) := Finset.measurableSet A
  let C : Set (Fin (N n) × α) := Prod.fst ⁻¹' (A : Set (Fin (N n)))
  have hC : MeasurableSet C := measurable_fst hA
  have hmassEq : π.law.real C = (uniformFiniteMeasure (Fin (N n))).real (A : Set (Fin (N n))) :=
    congrArg ENNReal.toReal (π.fst_mp.measure_preimage hA.nullMeasurableSet)
  have hmass : π.law.real C ∈ Icc ρ (1-ρ) := by
    rw [hmassEq, uniformFiniteMeasure_finset A]
    constructor
    · exact (le_div_iff₀ hnR).mpr hAlow
    · exact (div_le_iff₀ hnR).mpr hAhigh
  have hcost : Graphon.cutNormDiff
      (Graphon.pullback (finiteGraphon (G n c)) Prod.fst π.fst_mp)
      (Graphon.pullback (W c) Prod.snd π.snd_mp) ≤ σ/2 := (hπ c).le
  have hcut := aligned_cut_lower
    (Graphon.pullback (finiteGraphon (G n c)) Prod.fst π.fst_mp)
    (W c) Prod.snd π.snd_mp hbound hcost C hC hmass
  dsimp only [C] at hcut
  rw [← Set.preimage_compl, rectIntegral_pullback_preimage
    (finiteGraphon (G n c)) Prod.fst π.fst_mp hA hA.compl,
    finiteGraphon_cutIntegral (G n c) A] at hcut
  have hh := (le_div_iff₀ (sq_pos_of_pos hnR)).mp hcut
  nlinarith only [hh]

end ComponentTransfer.Lifting
