import HadwigerRamsey4Col.RealizationCounting

open scoped BigOperators Classical
open MeasureTheory Finset Set Filter

namespace HadwigerRamsey4Col.Realization

lemma prod_ite_subset {ι : Type*} [DecidableEq ι] (T s : Finset ι) (hs : s ⊆ T)
    (f g : ι → ℝ) :
    (∏ e ∈ T, if e ∈ s then g e else f e) = (∏ e ∈ T \ s, f e) * ∏ e ∈ s, g e := by
  conv_lhs => rw [← Finset.sdiff_union_of_subset hs]
  rw [Finset.prod_union (Finset.disjoint_left.mpr (fun e he hs => (Finset.mem_sdiff.mp he).2 hs))]
  congr 1
  · apply prod_congr rfl
    intro e he
    simp [(mem_sdiff.mp he).2]
  · apply prod_congr rfl
    intro e he
    simp [he]

/-- A product of signed graphon differences is controlled by one distinguished
cut error. Expanding the remaining edges costs a factor two per edge. -/
theorem residual_product_integral_le {α V : Type*} [MeasurableSpace α]
    [Fintype V] [DecidableEq V] {μ : Measure α} [IsProbabilityMeasure μ]
    (U W : Sym2 V → Graphon α μ) (T : Finset (Sym2 V)) (e₀ : Sym2 V)
    (he₀ : e₀ ∉ T) (hT : ∀ e ∈ T, (Quot.out e).1 ≠ (Quot.out e).2)
    (he : (Quot.out e₀).1 ≠ (Quot.out e₀).2) :
    |∫ x : V → α,
      (∏ e ∈ T, ((U e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
        (W e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))) *
      ((U e₀).toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2) -
        (W e₀).toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2))
      ∂Measure.pi (fun _ => μ)| ≤
        (2 : ℝ)^T.card * Graphon.cutNormDiff (U e₀) (W e₀) := by
  let F (s : Finset (Sym2 V)) (e : Sym2 V) : Graphon α μ := if e ∈ s then W e else U e
  let term (s : Finset (Sym2 V)) (x : V → α) : ℝ :=
    (∏ e ∈ T, (F s e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2)) *
      ((U e₀).toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2) -
        (W e₀).toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2))
  have hint (s) : Integrable (term s) (Measure.pi (fun _ => μ)) := by
    simpa only [Finset.prod_singleton, term] using
      Graphon.counting_integrable_term (U e₀) (W e₀) {e₀} T (F s)
        (by simpa only [Finset.mem_singleton, forall_eq]) hT
  have hb (s) : |∫ x, term s x ∂Measure.pi (fun _ => μ)| ≤
      Graphon.cutNormDiff (U e₀) (W e₀) :=
    Graphon.weighted_prod_graphon_diff_le (U e₀) (W e₀) T e₀ he₀ (F s) hT he
  have heq (x : V → α) :
      (∏ e ∈ T, ((U e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
        (W e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))) *
        ((U e₀).toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2) -
          (W e₀).toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2)) =
      ∑ s ∈ T.powerset, (-1 : ℝ)^s.card * term s x := by
    rw [Finset.prod_sub, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    have hprod := prod_ite_subset T s (mem_powerset.mp hs)
      (fun e => (U e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))
      (fun e => (W e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))
    have hF : (∏ e ∈ T, (F s e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2)) =
        (∏ e ∈ T \ s, (U e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2)) *
        ∏ e ∈ s, (W e).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) := by
      rw [← hprod]
      apply Finset.prod_congr rfl
      intro e he
      by_cases hh : e ∈ s <;> simp [F, hh]
    dsimp only [term]
    rw [hF]
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ (fun s _ => (hint s).const_mul _)]
  simp_rw [integral_const_mul]
  calc
    |∑ s ∈ T.powerset, (-1 : ℝ)^s.card * ∫ x, term s x ∂Measure.pi (fun _ => μ)|
      ≤ ∑ s ∈ T.powerset,
        |(-1 : ℝ)^s.card * ∫ x, term s x ∂Measure.pi (fun _ => μ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ T.powerset, Graphon.cutNormDiff (U e₀) (W e₀) := by
      apply Finset.sum_le_sum
      intro s hs
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hb s
    _ = _ := by simp

end HadwigerRamsey4Col.Realization
