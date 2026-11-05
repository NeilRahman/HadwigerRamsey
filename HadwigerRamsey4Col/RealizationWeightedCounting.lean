import HadwigerRamsey4Col.RealizationCounting
import Mathlib.MeasureTheory.Integral.Pi

open scoped BigOperators
open MeasureTheory Set Filter Finset

namespace HadwigerRamsey4Col.Realization

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
variable [Fintype V] [DecidableEq V]

/-- A set indicator represented by a symmetric rank-one graphon. -/
noncomputable def indicatorGraphon (A : Set α) (hA : MeasurableSet A) : Graphon α μ := by
  let f : α × α → ℝ := fun p => A.indicator (fun _ => 1) p.1 * A.indicator (fun _ => 1) p.2
  have hf : AEStronglyMeasurable f (μ.prod μ) :=
    (((measurable_const.indicator hA).comp measurable_fst).mul
      ((measurable_const.indicator hA).comp measurable_snd)).aestronglyMeasurable
  refine ⟨⟨AEEqFun.mk f hf, ?_⟩, ?_⟩
  · filter_upwards [AEEqFun.coeFn_mk f hf, ae_prod_swap (AEEqFun.coeFn_mk f hf)] with p hp hs
    rw [hp, hs]
    exact mul_comm _ _
  · filter_upwards [AEEqFun.coeFn_mk f hf] with p hp
    rw [hp]
    dsimp only [f]
    by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;> simp [h1,h2]

lemma indicatorGraphon_ae (A : Set α) (hA : MeasurableSet A) :
    ∀ᵐ p ∂μ.prod μ, (indicatorGraphon (μ := μ) A hA).toAEEqFun p =
      A.indicator (fun _ => 1) p.1 * A.indicator (fun _ => 1) p.2 :=
  AEEqFun.coeFn_mk _ _

lemma pair_measurePreserving {W : Type*} [Fintype W] (u v : W) (huv : u ≠ v) :
    MeasurePreserving (fun x : W → α => (x u, x v))
      (Measure.pi (fun _ : W => μ)) (μ.prod μ) := by
  refine ⟨(measurable_pi_apply _).prodMk (measurable_pi_apply _), ?_⟩
  have hi := (ProbabilityTheory.iIndepFun_pi (μ := fun _ : W => μ)
    (fun _ => aemeasurable_id)).indepFun huv
  simp only [id_eq] at hi
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable] at hi
  rw [hi, (measurePreserving_eval (fun _ : W => μ) _).map_eq,
    (measurePreserving_eval (fun _ : W => μ) _).map_eq]

lemma edge_eval_mk {W : Type*} [Fintype W] (G : Graphon α μ)
    (u v : W) (huv : u ≠ v) :
    ∀ᵐ x ∂Measure.pi (fun _ : W => μ),
      G.toAEEqFun (x (Quot.out (s(u,v))).1, x (Quot.out (s(u,v))).2) =
        G.toAEEqFun (x u, x v) := by
  have hrel : Sym2.Rel W (Quot.out (s(u,v))) (u,v) :=
    (Equivalence.quot_mk_eq_iff Sym2.Rel.is_equivalence _ _).mp (Quot.out_eq _)
  rcases Sym2.rel_iff'.mp hrel with h | h
  · exact Eventually.of_forall (fun x => by rw [h])
  · filter_upwards [(pair_measurePreserving (μ := μ) u v huv).quasiMeasurePreserving.ae G.symm_ae]
      with x hx
    simpa only [h, Prod.swap] using hx

noncomputable def originalEdge : Sym2 V ↪ Sym2 (V ⊕ V) :=
  (Function.Embedding.inl : V ↪ V ⊕ V).sym2Map

noncomputable def pendantEdge : V ↪ Sym2 (V ⊕ V) where
  toFun v := s(Sum.inl v, Sum.inr v)
  inj' := by
    intro v w h
    simpa only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, and_self, and_false, or_false] using h

noncomputable def augmentedKernel (U : Sym2 V → Graphon α μ)
    (A : V → Set α) (hA : ∀ v, MeasurableSet (A v)) : Sym2 (V ⊕ V) → Graphon α μ :=
  Sym2.lift ⟨fun x y => match x, y with
    | Sum.inl u, Sum.inl v => U s(u,v)
    | Sum.inl u, Sum.inr _ => indicatorGraphon (A u) (hA u)
    | Sum.inr _, Sum.inl v => indicatorGraphon (A v) (hA v)
    | Sum.inr _, Sum.inr _ => Graphon.zero,
    by intro x y; cases x <;> cases y <;> simp [Sym2.eq_swap]⟩

@[simp] lemma augmentedKernel_original (U : Sym2 V → Graphon α μ)
    (A : V → Set α) (hA : ∀ v, MeasurableSet (A v)) (e : Sym2 V) :
    augmentedKernel U A hA (originalEdge e) = U e := by
  induction e using Sym2.inductionOn with
  | _ u v => rfl

@[simp] lemma augmentedKernel_pendant (U : Sym2 V → Graphon α μ)
    (A : V → Set α) (hA : ∀ v, MeasurableSet (A v)) (v : V) :
    augmentedKernel U A hA (pendantEdge v) = indicatorGraphon (A v) (hA v) := rfl

lemma original_pendant_disjoint (S : Finset (Sym2 V)) :
    Disjoint (univ.map (pendantEdge (V := V))) (S.map originalEdge) := by
  apply Finset.disjoint_left.mpr
  intro e he hS
  obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨f, hf, heq⟩ := Finset.mem_map.mp hS
  induction f using Sym2.inductionOn with
  | _ u w =>
    change s(Sum.inl u, Sum.inl w) = s(Sum.inl v, Sum.inr v) at heq
    simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inl_ne_inr, and_false, false_and,
      or_self] at heq

lemma originalEdge_out_ne (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2) :
    ∀ e ∈ S.map originalEdge, (Quot.out e).1 ≠ (Quot.out e).2 := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
  intro heq
  have hout : s((Quot.out f).1, (Quot.out f).2) = f := Quot.out_eq f
  have hmap : s(Sum.inl (Quot.out f).1, Sum.inl (Quot.out f).2) = originalEdge f := by
    exact congrArg (Sym2.map Sum.inl) hout
  have houtmap : s((Quot.out (originalEdge f)).1,(Quot.out (originalEdge f)).2) =
      originalEdge f := Quot.out_eq _
  rw [heq, ← hmap, Sym2.eq_iff] at houtmap
  rcases houtmap with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact hS f hf (Sum.inl_injective (h1.symm.trans h2))
  · exact hS f hf (Sum.inl_injective (h2.symm.trans h1))

lemma pendantEdge_out_ne :
    ∀ e ∈ univ.map (pendantEdge (V := V)), (Quot.out e).1 ≠ (Quot.out e).2 := by
  intro e he
  obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp he
  intro heq
  have hout : s((Quot.out (pendantEdge v)).1,(Quot.out (pendantEdge v)).2) =
      pendantEdge v := Quot.out_eq _
  change s((Quot.out (pendantEdge v)).1,(Quot.out (pendantEdge v)).2) =
      s(Sum.inl v,Sum.inr v) at hout
  rw [heq, Sym2.eq_iff] at hout
  rcases hout with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Sum.inl_ne_inr (h1.symm.trans h2)
  · exact Sum.inl_ne_inr (h2.symm.trans h1)


lemma pendant_product_ae (U : Sym2 V → Graphon α μ)
    (A : V → Set α) (hA : ∀ v, MeasurableSet (A v)) :
    ∀ᵐ x ∂Measure.pi (fun _ : V ⊕ V => μ),
      (∏ e ∈ univ.map (pendantEdge (V := V)),
        (augmentedKernel U A hA e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) =
      (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x (Sum.inl v))) *
        ∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x (Sum.inr v)) := by
  have hv (v : V) : ∀ᵐ x ∂Measure.pi (fun _ : V ⊕ V => μ),
      (augmentedKernel U A hA (pendantEdge v)).toAEEqFun
        (x (Quot.out (pendantEdge v)).1, x (Quot.out (pendantEdge v)).2) =
      (A v).indicator (fun _ => (1 : ℝ)) (x (Sum.inl v)) *
        (A v).indicator (fun _ => (1 : ℝ)) (x (Sum.inr v)) := by
    simp only [augmentedKernel_pendant]
    filter_upwards [edge_eval_mk (indicatorGraphon (μ := μ) (A v) (hA v))
      (Sum.inl v) (Sum.inr v) (by simp),
      (pair_measurePreserving (μ := μ) (Sum.inl v) (Sum.inr v) (by simp)).quasiMeasurePreserving.ae
        (indicatorGraphon_ae (μ := μ) (A v) (hA v))] with x hx hy
    exact hx.trans hy
  filter_upwards [Filter.eventually_all.mpr hv] with x hx
  rw [Finset.prod_map, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun v _ => hx v)

lemma original_product_ae (S : Finset (Sym2 V)) (U : Sym2 V → Graphon α μ)
    (A : V → Set α) (hA : ∀ v, MeasurableSet (A v))
    (hS : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2) :
    ∀ᵐ x ∂Measure.pi (fun _ : V ⊕ V => μ),
      (∏ e ∈ S.map originalEdge,
        (augmentedKernel U A hA e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) =
      ∏ e ∈ S, (U e).toAEEqFun
        (x (Sum.inl (Quot.out e).1), x (Sum.inl (Quot.out e).2)) := by
  have he (e : Sym2 V) (he : e ∈ S) : ∀ᵐ x ∂Measure.pi (fun _ : V ⊕ V => μ),
      (augmentedKernel U A hA (originalEdge e)).toAEEqFun
        (x (Quot.out (originalEdge e)).1, x (Quot.out (originalEdge e)).2) =
      (U e).toAEEqFun (x (Sum.inl (Quot.out e).1), x (Sum.inl (Quot.out e).2)) := by
    simp only [augmentedKernel_original]
    have hmap : originalEdge e = s(Sum.inl (Quot.out e).1, Sum.inl (Quot.out e).2) :=
      (congrArg (Sym2.map Sum.inl) (Quot.out_eq e)).symm
    rw [hmap]
    exact edge_eval_mk (U e) _ _ (fun h => hS e he (Sum.inl_injective h))
  filter_upwards [(S.eventually_all).mpr he] with x hx
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl (fun e he => hx e he)

/-- Integrating out one pendant vertex per test vertex realizes all set indicators. -/
lemma pendant_integral_identity (S : Finset (Sym2 V)) (U : Sym2 V → Graphon α μ)
    (A : V → Set α) (hA : ∀ v, MeasurableSet (A v))
    (hS : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2) :
    (∫ x : V ⊕ V → α,
      (∏ e ∈ univ.map (pendantEdge (V := V)),
        (augmentedKernel U A hA e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S.map originalEdge,
        (augmentedKernel U A hA e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      ∂Measure.pi (fun _ => μ)) =
    (∫ x : V → α,
      (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)) *
      (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      ∂Measure.pi (fun _ => μ)) * ∏ v, μ.real (A v) := by
  let f : (V → α) → ℝ := fun x =>
    (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)) *
    (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
  let g : (V → α) → ℝ := fun x => ∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)
  have heq : (∫ x : V ⊕ V → α,
      (∏ e ∈ univ.map (pendantEdge (V := V)),
        (augmentedKernel U A hA e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S.map originalEdge,
        (augmentedKernel U A hA e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      ∂Measure.pi (fun _ => μ)) =
      ∫ x : V ⊕ V → α, f (fun v => x (Sum.inl v)) * g (fun v => x (Sum.inr v))
        ∂Measure.pi (fun _ => μ) := by
    apply integral_congr_ae
    filter_upwards [pendant_product_ae U A hA, original_product_ae S U A hA hS] with x hx hy
    rw [hx,hy]
    dsimp [f,g]
    ring
  rw [heq]
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : V ⊕ V => μ)
  have hc := hmp.integral_comp' (fun x : (V → α) × (V → α) => f x.1 * g x.2)
  change (∫ x, f (fun v => x (Sum.inl v)) * g (fun v => x (Sum.inr v))
    ∂Measure.pi (fun _ : V ⊕ V => μ)) = _ at hc
  rw [hc, integral_prod_mul]
  congr 1
  change (∫ x : V → α, ∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)
    ∂Measure.pi (fun _ => μ)) = _
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [integral_indicator (hA v), setIntegral_const]
  simp [measureReal_def]


/-- The counting lemma with measurable positive-measure vertex classes.
The fixed denominator is harmless for convergence and avoids requiring a
separate endpoint-conditioning argument for vertex weights. -/
theorem vertex_weighted_counting (S : Finset (Sym2 V))
    (U W : Sym2 V → Graphon α μ)
    (hS : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2)
    (A : V → Set α) (hA : ∀ v, MeasurableSet (A v))
    (hpos : ∀ v, 0 < μ.real (A v)) :
    |(∫ x : V → α,
      (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)) *
      (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      ∂Measure.pi (fun _ => μ)) -
     (∫ x : V → α,
      (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)) *
      (∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      ∂Measure.pi (fun _ => μ))| ≤
      (∑ e ∈ S, Graphon.cutNormDiff (U e) (W e)) / ∏ v, μ.real (A v) := by
  let R := univ.map (pendantEdge (V := V))
  let T := S.map originalEdge
  have hdis : Disjoint R T := original_pendant_disjoint S
  have hRT : ∀ e ∈ R ∪ T, (Quot.out e).1 ≠ (Quot.out e).2 := by
    intro e he
    rcases mem_union.mp he with h | h
    · exact pendantEdge_out_ne e h
    · exact originalEdge_out_ne S hS e h
  have h := Graphon.heterogeneous_homDensity_sub_le (R ∪ T)
    (augmentedKernel U A hA) (augmentedKernel W A hA) hRT
  have hu : (∫ x : V ⊕ V → α,
      ∏ e ∈ R ∪ T, (augmentedKernel U A hA e).toAEEqFun
        (x (Quot.out e).1, x (Quot.out e).2) ∂Measure.pi (fun _ => μ)) =
      (∫ x : V → α,
        (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)) *
        (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
        ∂Measure.pi (fun _ => μ)) * ∏ v, μ.real (A v) := by
    simp_rw [Finset.prod_union hdis]
    exact pendant_integral_identity S U A hA hS
  have hw : (∫ x : V ⊕ V → α,
      ∏ e ∈ R ∪ T, (augmentedKernel W A hA e).toAEEqFun
        (x (Quot.out e).1, x (Quot.out e).2) ∂Measure.pi (fun _ => μ)) =
      (∫ x : V → α,
        (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)) *
        (∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
        ∂Measure.pi (fun _ => μ)) * ∏ v, μ.real (A v) := by
    simp_rw [Finset.prod_union hdis]
    exact pendant_integral_identity S W A hA hS
  have hsum : (∑ e ∈ R ∪ T,
      Graphon.cutNormDiff (augmentedKernel U A hA e) (augmentedKernel W A hA e)) =
      ∑ e ∈ S, Graphon.cutNormDiff (U e) (W e) := by
    rw [Finset.sum_union hdis]
    simp only [R, T, Finset.sum_map, augmentedKernel_original, augmentedKernel_pendant,
      Graphon.cutNormDiff_self, Finset.sum_const_zero, zero_add]
  rw [hu,hw,hsum, ← sub_mul, abs_mul, abs_of_pos (Finset.prod_pos (fun v _ => hpos v))] at h
  exact (le_div_iff₀ (Finset.prod_pos (fun v _ => hpos v))).mpr h

end HadwigerRamsey4Col.Realization
