import HadwigerRamsey4Col.TransferCompactnessNet
import HadwigerRamsey4Col.Ramsey
import HadwigerRamsey4Col.LiftingFiniteCut

open MeasureTheory Filter Set Finset Graphon
open scoped BigOperators Topology Classical ENNReal unitInterval
open HadwigerRamsey4Col.Realization HadwigerRamsey4Col.Lifting

namespace HadwigerRamsey4Col.Transfer

/-- Uniform finite vertices have a common measurable presentation on the
unit interval. The extra interval coordinate makes the source atomless. -/
theorem exists_uniform_vertex_map (n : ℕ) [Nonempty (Fin n)] :
    ∃ cell : I → Fin n, MeasurePreserving cell volume (uniformFiniteMeasure (Fin n)) := by
  let ν := (uniformFiniteMeasure (Fin n)).prod (volume : Measure I)
  obtain ⟨eI⟩ := Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval
    I (volume : Measure I)
  obtain ⟨eF⟩ := Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval
    (Fin n × I) ν
  have hI : MeasurePreserving eI.toFun (volume : Measure I) (volume.restrict (Set.Icc 0 1)) :=
    ⟨eI.measurable_toFun,eI.map_toFun⟩
  have hF : MeasurePreserving eF.invFun (volume.restrict (Set.Icc 0 1)) ν :=
    ⟨eF.measurable_invFun,eF.map_invFun⟩
  exact ⟨Prod.fst ∘ eF.invFun ∘ eI.toFun,measurePreserving_fst.comp (hF.comp hI)⟩

lemma sum_adjIndicator {r n : ℕ} (G : Fin r → SimpleGraph (Fin n))
    (hG : IsDecomposition G) (u v : Fin n) :
    (∑ c, Graphon.adjIndicator (G c) u v) = if u = v then 0 else 1 := by
  by_cases huv : u = v
  · subst v
    simp [Graphon.adjIndicator]
  · rw [if_neg huv]
    obtain ⟨c,hc,hunique⟩ := hG u v huv
    rw [Finset.sum_eq_single c]
    · simp [Graphon.adjIndicator,hc]
    · intro b hb hbc
      have hn : ¬ (G b).Adj u v := fun h => hbc (hunique b h)
      simp [Graphon.adjIndicator,hn]
    · simp

/-- Vanishing rectangle integrals force a real integrable kernel to vanish.
This is the standard product pi-lambda uniqueness argument. -/
lemma ae_zero_of_rect_integrals {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (f : α × α → ℝ) (hf : Integrable f (μ.prod μ))
    (hrect : ∀ S T : Set α, MeasurableSet S → MeasurableSet T →
      ∫ p in S ×ˢ T, f p ∂μ.prod μ = 0) : f =ᵐ[μ.prod μ] 0 := by
  apply hf.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro E hE _
  let C := {s : Set α | MeasurableSet s}
  have hgen : (inferInstance : MeasurableSpace (α × α)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) C C) :=
    (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet
      MeasurableSpace.generateFrom_measurableSet isCountablySpanning_measurableSet
      isCountablySpanning_measurableSet).symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) C C) :=
    IsPiSystem.prod (fun _ ha _ hb _ => MeasurableSet.inter ha hb)
      (fun _ ha _ hb _ => MeasurableSet.inter ha hb)
  have htotal := hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  simp only [Set.univ_prod_univ,setIntegral_univ] at htotal
  exact MeasurableSpace.induction_on_inter hgen hpi (by simp)
    (fun E' hE' => by
      obtain ⟨S,hS,T,hT,rfl⟩ := Set.mem_image2.mp hE'
      exact hrect S T hS hT)
    (fun E' hE' hz => by have h := integral_add_compl hE' hf; linarith)
    (fun s hd hm hz => by rw [integral_iUnion hm hd hf.integrableOn]; simp [hz]) E hE

/-- Common cut-norm limits preserve the colour simplex whenever the sum of
the approximating colours differs from one by a vanishing L1 error. -/
theorem limit_sum_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r : ℕ}
    (U : ℕ → Fin r → Graphon α μ) (W : Fin r → Graphon α μ)
    (hcut : ∀ c, Tendsto (fun n => cutNormDiff (U n c) (W c)) atTop (𝓝 0))
    (herror : Tendsto (fun n => ∫ p, |(∑ c, (U n c).toAEEqFun p)-1| ∂μ.prod μ)
      atTop (𝓝 0)) :
    ∀ᵐ p ∂μ.prod μ, (∑ c, (W c).toAEEqFun p) = 1 := by
  let f : α × α → ℝ := fun p => (∑ c, (W c).toAEEqFun p)-1
  have hf : Integrable f (μ.prod μ) :=
    (integrable_finsetSum _ (fun c _ => SymmKernel.graphon_integrable (W c))).sub (integrable_const 1)
  have hrect (S T : Set α) (hS : MeasurableSet S) (hT : MeasurableSet T) :
      ∫ p in S ×ˢ T, f p ∂μ.prod μ = 0 := by
    have hlim (c) : Tendsto (fun n => (U n c).toSymmKernel.rectIntegral S T) atTop
        (𝓝 ((W c).toSymmKernel.rectIntegral S T)) := by
      have hbound (n : ℕ) : ‖rectIntegralDiff (U n c) (W c) S T‖ ≤ cutNormDiff (U n c) (W c) := by
        rw [Real.norm_eq_abs]
        exact Graphon.abs_rectIntegralDiff_le (U n c) (W c) hS hT
      have hd : Tendsto (fun n => rectIntegralDiff (U n c) (W c) S T) atTop (𝓝 0) :=
        squeeze_zero_norm hbound (hcut c)
      simpa only [rectIntegralDiff_eq,sub_add_cancel,zero_add] using
        hd.add_const ((W c).toSymmKernel.rectIntegral S T)
    have hu := (tendsto_finsetSum Finset.univ (fun c _ => hlim c)).sub_const
      (∫ _p in S ×ˢ T, (1 : ℝ) ∂μ.prod μ)
    have hEq (n) : (∑ c, (U n c).toSymmKernel.rectIntegral S T)-
        (∫ _p in S ×ˢ T, (1 : ℝ) ∂μ.prod μ) =
        ∫ p in S ×ˢ T, (∑ c, (U n c).toAEEqFun p)-1 ∂μ.prod μ := by
      rw [integral_sub]
      · rw [integral_finsetSum]
        · rfl
        · intro c hc; exact (SymmKernel.graphon_integrable (U n c)).integrableOn
      · exact integrable_finsetSum _ (fun c _ => (SymmKernel.graphon_integrable (U n c)).integrableOn)
      · exact integrable_const 1
    have hEqW : (∑ c, (W c).toSymmKernel.rectIntegral S T)-
        (∫ _p in S ×ˢ T, (1 : ℝ) ∂μ.prod μ) = ∫ p in S ×ˢ T, f p ∂μ.prod μ := by
      rw [show (∫ p in S ×ˢ T, f p ∂μ.prod μ) =
        (∫ p in S ×ˢ T, ∑ c, (W c).toAEEqFun p ∂μ.prod μ)-
        (∫ _p in S ×ˢ T, (1 : ℝ) ∂μ.prod μ) from
          integral_sub (integrable_finsetSum _ (fun c _ => (SymmKernel.graphon_integrable (W c)).integrableOn))
            (integrable_const 1)]
      rw [integral_finsetSum _ (fun c _ => (SymmKernel.graphon_integrable (W c)).integrableOn)]
      rfl
    simp_rw [hEq,hEqW] at hu
    have hz : Tendsto (fun n => ∫ p in S ×ˢ T, (∑ c, (U n c).toAEEqFun p)-1 ∂μ.prod μ)
        atTop (𝓝 0) := by
      apply squeeze_zero_norm _ herror
      intro n
      rw [Real.norm_eq_abs]
      apply abs_integral_le_integral_abs.trans
      apply setIntegral_le_integral
      · exact ((integrable_finsetSum _ (fun c _ => SymmKernel.graphon_integrable (U n c))).sub
          (integrable_const 1)).abs
      · exact Eventually.of_forall (fun _ => abs_nonneg _)
    exact tendsto_nhds_unique hu hz
  have hz := ae_zero_of_rect_integrals f hf hrect
  filter_upwards [hz] with p hp
  exact sub_eq_zero.mp hp

lemma uniform_diagonal_integral (n : ℕ) [Nonempty (Fin n)] :
    (∫ q : Fin n × Fin n, if q.1=q.2 then (1 : ℝ) else 0
      ∂(uniformFiniteMeasure (Fin n)).prod (uniformFiniteMeasure (Fin n))) = 1/(n : ℝ) := by
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [integral_uniform_eq_expect uniformFiniteMeasure_singleton,
    Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ,Fintype.card_fin]
  simp
  have hnNat : 0 < n := by simpa using (Fintype.card_pos (α := Fin n))
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hnNat.ne'
  field_simp

lemma presentation_sum_error {r n : ℕ} [Nonempty (Fin n)]
    (G : Fin r → SimpleGraph (Fin n)) (hG : IsDecomposition G)
    (cell : I → Fin n) (hcell : MeasurePreserving cell volume (uniformFiniteMeasure (Fin n))) :
    (∫ p, |(∑ c, (pullback (finiteGraphon (G c)) cell hcell).toAEEqFun p)-1|
      ∂(volume : Measure I).prod volume) = 1/(n : ℝ) := by
  have hraw : ∀ᵐ p ∂(volume : Measure I).prod volume, ∀ c,
      (pullback (finiteGraphon (G c)) cell hcell).toAEEqFun p =
        adjIndicator (G c) (cell p.1) (cell p.2) := by
    rw [Filter.eventually_all]
    intro c
    filter_upwards [pullback_ae (finiteGraphon (G c)) cell hcell] with p hp
    rw [hp]
    exact markedGraphon_uniform_apply uniformFiniteMeasure_singleton
      (adjIndicator (G c)) (adjIndicator_symm_all (G c)) (adjIndicator_bounds_all (G c))
      id measurable_id (cell p.1) (cell p.2)
  calc
    _ = ∫ p, if cell p.1=cell p.2 then (1 : ℝ) else 0
        ∂(volume : Measure I).prod volume := by
      apply integral_congr_ae
      filter_upwards [hraw] with p hp
      simp_rw [hp]
      rw [sum_adjIndicator G hG]
      split_ifs <;> norm_num
    _ = ∫ q : Fin n × Fin n, if q.1=q.2 then (1 : ℝ) else 0
        ∂(uniformFiniteMeasure (Fin n)).prod (uniformFiniteMeasure (Fin n)) := by
      have hmp := hcell.prod hcell
      rw [← hmp.map_eq]
      have hm : Measurable (fun q : Fin n × Fin n => if q.1=q.2 then (1 : ℝ) else 0) :=
        Measurable.of_discrete
      exact (integral_map hmp.measurable.aemeasurable hm.aestronglyMeasurable).symm
    _ = _ := uniform_diagonal_integral n

/-- Common coloured compactness of complete finite graph colourings. The
unit-interval presentation is shared by all colours and its missing diagonal
has mass tending to zero, so the limiting colours sum to one almost everywhere. -/
theorem finite_coloured_compactness_pos {r : ℕ}
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (hG : ∀ n, IsDecomposition (G n)) :
    ∃ (W : Fin r → GraphonI) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᵐ p ∂(volume : Measure I).prod volume, (∑ c, (W c).toAEEqFun p) = 1) ∧
      FiniteGraphCommonCutConverges (volume : Measure I) (N ∘ φ) (fun n => G (φ n)) W := by
  haveI (n : ℕ) : Nonempty (Fin (N n)) := ⟨⟨0,hNpos n⟩⟩
  choose cell hcell using fun n => exists_uniform_vertex_map (N n)
  let U : ℕ → Fin r → GraphonI := fun n c => pullback (finiteGraphon (G n c)) (cell n) (hcell n)
  obtain ⟨W,φ,hφ,e,he,hcut⟩ := compact_of_common_nets
    (common_finite_nets (μ := (volume : Measure I)) r) U
  let V : ℕ → Fin r → GraphonI := fun n c => pullback (U (φ n) c) (e n) (he n)
  have hV (n c) : V n c = pullback (finiteGraphon (G (φ n) c))
      (cell (φ n) ∘ e n) ((hcell (φ n)).comp (he n)) :=
    pullback_pullback (finiteGraphon (G (φ n) c)) (cell (φ n)) (hcell (φ n)) (e n) (he n)
  have herror : Tendsto (fun n => ∫ p, |(∑ c, (V n c).toAEEqFun p)-1|
      ∂(volume : Measure I).prod volume) atTop (𝓝 0) := by
    have heq (n) : (∫ p, |(∑ c, (V n c).toAEEqFun p)-1|
        ∂(volume : Measure I).prod volume) = 1/(N (φ n) : ℝ) := by
      simp_rw [hV]
      exact presentation_sum_error (G (φ n)) (hG (φ n))
        (cell (φ n) ∘ e n) ((hcell (φ n)).comp (he n))
    simp_rw [heq]
    have ht : Tendsto (fun n => (N (φ n) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (hN.comp hφ.tendsto_atTop)
    have hi : Tendsto (fun n => (N (φ n) : ℝ)⁻¹) atTop (𝓝 0) := ht.inv_tendsto_atTop
    simpa only [one_div] using hi
  refine ⟨W,φ,hφ,limit_sum_one V W hcut herror,?_⟩
  intro ε hε
  have hevent : ∀ᶠ n in atTop, ∀ c, cutNormDiff (V n c) (W c) < ε := by
    rw [Filter.eventually_all]
    intro c
    exact (tendsto_order.mp (hcut c)).2 ε hε
  filter_upwards [hevent] with n hn
  let f := cell (φ n) ∘ e n
  have hf : MeasurePreserving f volume (uniformFiniteMeasure (Fin (N (φ n)))) :=
    (hcell (φ n)).comp (he n)
  refine ⟨⟨⟨0,hNpos (φ n)⟩⟩,ProbabilityCoupling.ofMaps (volume : Measure I) f hf id (MeasurePreserving.id _),fun c => ?_⟩
  rw [ProbabilityCoupling.ofMaps_cost,pullback_id]
  change cutNormDiff (pullback (finiteGraphon (G (φ n) c)) f hf) (W c) < ε
  have hh := hn c
  rw [hV n c] at hh
  exact hh

end HadwigerRamsey4Col.Transfer
