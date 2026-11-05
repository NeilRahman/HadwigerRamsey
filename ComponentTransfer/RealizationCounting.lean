/-
Adapted from Cameron Freer’s Graphon/Counting.lean, copyright (c) 2026.
Released under Apache 2.0; see vendor/graphon/LICENSE.
The extension permits a different kernel at every test edge.
-/
import Graphon.Counting

open MeasureTheory Set Filter Finset SimpleGraph
open scoped ENNReal

namespace Graphon
variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
variable [IsProbabilityMeasure μ] [Fintype V] [DecidableEq V]

lemma heterogeneous_integrable_term (U W : Sym2 V → Graphon α μ)
    (S R : Finset (Sym2 V)) (f : Sym2 V → Graphon α μ)
    (hS_edges : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2)
    (hR_edges : ∀ e ∈ R, (Quot.out e).1 ≠ (Quot.out e).2) :
    Integrable (fun x : V → α =>
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)))
      (Measure.pi (fun _ => μ)) := by
  -- The integrand is a product of [0,1]-valued terms times a difference in [-1,1],
  -- hence bounded in [-1,1]. On a finite measure space, bounded a.e. functions are integrable.
  -- Helper: graphon eval at an edge is AEMeasurable w.r.t. Measure.pi
  have graphon_eval_aem : ∀ (G : Graphon α μ) (e : Sym2 V),
      (Quot.out e).1 ≠ (Quot.out e).2 →
      AEMeasurable (fun x : V → α => G.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ => μ)) := by
    intro G e hne
    have h_pair : Measurable (fun x : V → α => (x (Quot.out e).1, x (Quot.out e).2)) :=
      Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
    have h_indep : ProbabilityTheory.iIndepFun (fun i (x : V → α) => x i)
        (Measure.pi (fun _ : V => μ)) :=
      ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
    have h_indep_pair := h_indep.indepFun hne
    have h_map : Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ : V => μ)) =
        (Measure.map (fun x => x (Quot.out e).1) (Measure.pi (fun _ : V => μ))).prod
        (Measure.map (fun x => x (Quot.out e).2) (Measure.pi (fun _ : V => μ))) := by
      rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable] at h_indep_pair
      exact h_indep_pair
    have h_marg₁ : Measure.map (fun x => x (Quot.out e).1) (Measure.pi (fun _ : V => μ)) = μ :=
      (MeasureTheory.measurePreserving_eval (fun _ : V => μ) (Quot.out e).1).map_eq
    have h_marg₂ : Measure.map (fun x => x (Quot.out e).2) (Measure.pi (fun _ : V => μ)) = μ :=
      (MeasureTheory.measurePreserving_eval (fun _ : V => μ) (Quot.out e).2).map_eq
    have h_map_eq : Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ : V => μ)) = μ.prod μ := by
      rw [h_map, h_marg₁, h_marg₂]
    have h_aem_map : AEMeasurable G.toAEEqFun
        (Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
          (Measure.pi (fun _ : V => μ))) := by
      rw [h_map_eq]; exact G.toAEEqFun.aemeasurable
    exact h_aem_map.comp_measurable h_pair
  -- AEMeasurability of product over R
  have hR_aem : AEMeasurable (fun x : V → α =>
      ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) :=
    Finset.aemeasurable_fun_prod R (fun e he => graphon_eval_aem (f e) e (hR_edges e he))
  -- AEMeasurability of each product over S
  have hSU_aem : AEMeasurable (fun x : V → α =>
      ∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) :=
    Finset.aemeasurable_fun_prod S (fun e he => graphon_eval_aem (U e) e (hS_edges e he))
  have hSW_aem : AEMeasurable (fun x : V → α =>
      ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) :=
    Finset.aemeasurable_fun_prod S (fun e he => graphon_eval_aem (W e) e (hS_edges e he))
  -- AEMeasurability of the full integrand
  have h_aem : AEMeasurable (fun x : V → α =>
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)))
      (Measure.pi (fun _ => μ)) :=
    hR_aem.mul (hSU_aem.sub hSW_aem)
  -- A.e. bound: each graphon eval is in [0,1] a.e., so products are in [0,1],
  -- difference is in [-1,1], and the full product is in [-1,1].
  have h_ae_bound : ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) ∈
      Set.Icc (-1 : ℝ) 1 := by
    -- Collect a.e. bounds for all graphon evals at edges in R and S
    have hR_ae : ∀ e ∈ R, ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
      fun e he => graphonEval_mem_Icc_ae (f e) (hR_edges e he)
    have hSU_ae : ∀ e ∈ S, ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
      fun e he => graphonEval_mem_Icc_ae (U e) (hS_edges e he)
    have hSW_ae : ∀ e ∈ S, ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
      fun e he => graphonEval_mem_Icc_ae (W e) (hS_edges e he)
    have hR_all := (Filter.eventually_all_finite R.finite_toSet).mpr hR_ae
    have hSU_all := (Filter.eventually_all_finite S.finite_toSet).mpr hSU_ae
    have hSW_all := (Filter.eventually_all_finite S.finite_toSet).mpr hSW_ae
    filter_upwards [hR_all, hSU_all, hSW_all] with x hxR hxSU hxSW
    -- Now prove the pointwise bound
    have hR_prod_nn : 0 ≤ ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_nonneg (fun e he => (hxR e he).1)
    have hR_prod_le : ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 :=
      Finset.prod_le_one (fun e he => (hxR e he).1) (fun e he => (hxR e he).2)
    have hSU_prod_nn : 0 ≤ ∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_nonneg (fun e he => (hxSU e he).1)
    have hSU_prod_le : ∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 :=
      Finset.prod_le_one (fun e he => (hxSU e he).1) (fun e he => (hxSU e he).2)
    have hSW_prod_nn : 0 ≤ ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_nonneg (fun e he => (hxSW e he).1)
    have hSW_prod_le : ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 :=
      Finset.prod_le_one (fun e he => (hxSW e he).1) (fun e he => (hxSW e he).2)
    -- The difference is in [-1, 1]
    have h_diff_lower : -1 ≤ ∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
        ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by linarith
    have h_diff_upper : ∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
        ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 := by linarith
    -- Product of [0,1] and [-1,1] is in [-1,1]
    set pR := ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    set d := ∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
             ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    constructor
    · -- Lower bound: pR * d ≥ -1
      -- Since 0 ≤ pR ≤ 1 and -1 ≤ d ≤ 1, we have pR * d ≥ -1
      nlinarith [sq_nonneg pR, sq_nonneg d]
    · -- Upper bound: pR * d ≤ 1
      nlinarith [sq_nonneg pR, sq_nonneg d]
  exact Integrable.of_mem_Icc (-1) 1 h_aem h_ae_bound

theorem heterogeneous_weighted_homDensity_sub_le
    (U W : Sym2 V → Graphon α μ) (S : Finset (Sym2 V))
    (R : Finset (Sym2 V))
    (f : Sym2 V → Graphon α μ)
    (hRS : Disjoint R S)
    (hS_edges : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2)
    (hR_edges : ∀ e ∈ R, (Quot.out e).1 ≠ (Quot.out e).2) :
    |∫ x : V → α,
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
    ∂Measure.pi (fun _ => μ)| ≤ ∑ e ∈ S, cutNormDiff (U e) (W e) := by
  induction S using Finset.induction generalizing R f with
  | empty =>
    simp
  | @insert e₀ S' he₀ ih =>
    have he₀_edge : (Quot.out e₀).1 ≠ (Quot.out e₀).2 :=
      hS_edges e₀ (Finset.mem_insert_self e₀ S')
    have hS'_edges : ∀ e ∈ S', (Quot.out e).1 ≠ (Quot.out e).2 :=
      fun e he => hS_edges e (Finset.mem_insert_of_mem he)
    -- Key: e₀ ∉ R (from disjointness)
    have he₀R : e₀ ∉ R :=
      Finset.disjoint_right.mp hRS (Finset.mem_insert_self e₀ S')
    -- Set up R' = insert e₀ R, f' = Function.update f e₀ (U e₀)
    set R' := insert e₀ R with hR'_def
    set f' : Sym2 V → Graphon α μ := Function.update f e₀ (U e₀) with hf'_def
    -- Set up f'' for Term 2
    set f'' : Sym2 V → Graphon α μ := fun e => if e ∈ S' then W e else f e with hf''_def
    -- Algebraic identity: the integrand splits as Term1 + Term2
    have h_eq : ∀ x : V → α,
        (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (∏ e ∈ insert e₀ S', (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
         ∏ e ∈ insert e₀ S', (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) =
        ((∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
         (∏ e ∈ S', (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
          ∏ e ∈ S', (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))) +
        ((∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
         ((U e₀).toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
          (W e₀).toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2))) := by
      intro x
      -- Simplify prod over R' = insert e₀ R with f' (update)
      have hR'_prod : ∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          (U e₀).toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) *
          ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
        rw [hR'_def, Finset.prod_insert he₀R]
        congr 1
        · show (Function.update f e₀ (U e₀) e₀).toAEEqFun _ = _
          rw [Function.update_self]
        · apply Finset.prod_congr rfl
          intro e he
          show (Function.update f e₀ (U e₀) e).toAEEqFun _ = _
          have hne : e ≠ e₀ := fun heq => he₀R (heq ▸ he)
          rw [Function.update_of_ne hne]
      -- Simplify prod over R ∪ S' with f''
      have hRS'_prod : ∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
          (∏ e ∈ S', (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) := by
        rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hRS)]
        congr 1
        · apply Finset.prod_congr rfl
          intro e he
          simp only [hf''_def]
          have : e ∉ S' := Finset.disjoint_left.mp
            (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hRS) he
          simp [this]
        · apply Finset.prod_congr rfl
          intro e he; simp only [hf''_def, if_pos he]
      rw [hR'_prod, hRS'_prod, Finset.prod_insert he₀, Finset.prod_insert he₀]
      ring
    -- Integrability of both terms
    have hR'_edges : ∀ e ∈ R', (Quot.out e).1 ≠ (Quot.out e).2 := by
      intro e he; rw [hR'_def] at he
      rcases Finset.mem_insert.mp he with rfl | he'
      · exact he₀_edge
      · exact hR_edges e he'
    have hRS'_edges : ∀ e ∈ R ∪ S', (Quot.out e).1 ≠ (Quot.out e).2 := by
      intro e he; rcases Finset.mem_union.mp he with he' | he'
      · exact hR_edges e he'
      · exact hS'_edges e he'
    have h_int1 : Integrable (fun x : V → α =>
        (∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (∏ e ∈ S', (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
         ∏ e ∈ S', (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)))
        (Measure.pi (fun _ => μ)) :=
      heterogeneous_integrable_term U W S' R' f' hS'_edges hR'_edges
    have h_int2 : Integrable (fun x : V → α =>
        (∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
        ((U e₀).toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
         (W e₀).toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2)))
        (Measure.pi (fun _ => μ)) := by
      -- The integrand is bounded a.e. by 2 (product of [0,1] times [-1,1])
      -- on a probability space, so it is integrable.
      have h_aux := heterogeneous_integrable_term U W {e₀} (R ∪ S') f''
        (by intro e he; simp only [Finset.mem_singleton] at he; rw [he]; exact he₀_edge)
        hRS'_edges
      -- Convert ∏ e ∈ {e₀}, G_e(x) to G_{e₀}(x) via Finset.prod_singleton
      simp only [Finset.prod_singleton] at h_aux
      exact h_aux
    -- Rewrite using the algebraic identity
    simp_rw [h_eq]
    rw [integral_add h_int1 h_int2]
    -- Triangle inequality + bounds
    have hR'S'_disj : Disjoint R' S' := by
      rw [hR'_def]
      exact Finset.disjoint_insert_left.mpr ⟨he₀, hRS.mono_right (Finset.subset_insert _ _)⟩
    have he₀_not_RS' : e₀ ∉ R ∪ S' := by
      rw [Finset.mem_union, not_or]; exact ⟨he₀R, he₀⟩
    calc |∫ x, _ ∂_ + ∫ x, _ ∂_|
        ≤ |∫ x : V → α,
            (∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
            (∏ e ∈ S', (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
             ∏ e ∈ S', (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
            ∂Measure.pi (fun _ => μ)| +
          |∫ x : V → α,
            (∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
            ((U e₀).toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
             (W e₀).toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2))
            ∂Measure.pi (fun _ => μ)| := abs_add_le _ _
      _ ≤ (∑ e ∈ S', cutNormDiff (U e) (W e)) + cutNormDiff (U e₀) (W e₀) :=
          add_le_add (ih R' f' hR'S'_disj hS'_edges hR'_edges)
            (weighted_prod_graphon_diff_le (U e₀) (W e₀) (R ∪ S') e₀ he₀_not_RS' f''
              hRS'_edges he₀_edge)
      _ = ∑ e ∈ insert e₀ S', cutNormDiff (U e) (W e) := by
          rw [Finset.sum_insert he₀]; ring


/-- A heterogeneous finite product of graphon edge evaluations is integrable. -/
theorem heterogeneous_integrand_integrable
    (S : Finset (Sym2 V)) (U : Sym2 V → Graphon α μ)
    (hS : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2) :
    Integrable (fun x : V → α => ∏ e ∈ S,
      (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) := by
  have graphon_eval_aem : ∀ (G : Graphon α μ) (e : Sym2 V),
      (Quot.out e).1 ≠ (Quot.out e).2 →
      AEMeasurable (fun x : V → α => G.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ => μ)) := by
    intro G e hne
    have h_pair : Measurable (fun x : V → α => (x (Quot.out e).1, x (Quot.out e).2)) :=
      Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
    have h_indep : ProbabilityTheory.iIndepFun (fun i (x : V → α) => x i)
        (Measure.pi (fun _ : V => μ)) :=
      ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
    have h_indep_pair := h_indep.indepFun hne
    have h_map : Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ : V => μ)) =
        (Measure.map (fun x => x (Quot.out e).1) (Measure.pi (fun _ : V => μ))).prod
        (Measure.map (fun x => x (Quot.out e).2) (Measure.pi (fun _ : V => μ))) := by
      rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable] at h_indep_pair
      exact h_indep_pair
    have h_marg₁ : Measure.map (fun x => x (Quot.out e).1) (Measure.pi (fun _ : V => μ)) = μ :=
      (MeasureTheory.measurePreserving_eval (fun _ : V => μ) (Quot.out e).1).map_eq
    have h_marg₂ : Measure.map (fun x => x (Quot.out e).2) (Measure.pi (fun _ : V => μ)) = μ :=
      (MeasureTheory.measurePreserving_eval (fun _ : V => μ) (Quot.out e).2).map_eq
    have h_map_eq : Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ : V => μ)) = μ.prod μ := by
      rw [h_map, h_marg₁, h_marg₂]
    have h_aem_map : AEMeasurable G.toAEEqFun
        (Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
          (Measure.pi (fun _ : V => μ))) := by
      rw [h_map_eq]; exact G.toAEEqFun.aemeasurable
    exact h_aem_map.comp_measurable h_pair

  apply Integrable.of_mem_Icc 0 1
  · exact Finset.aemeasurable_fun_prod S (fun e he => graphon_eval_aem (U e) e (hS e he))
  · have hall := (Filter.eventually_all_finite S.finite_toSet).mpr
      (fun e he => graphonEval_mem_Icc_ae (U e) (hS e he))
    filter_upwards [hall] with x hx
    exact ⟨Finset.prod_nonneg (fun e he => (hx e he).1),
      Finset.prod_le_one (fun e he => (hx e he).1) (fun e he => (hx e he).2)⟩

/-- Counting bound for arbitrary colours or kernel decorations on the edges. -/
theorem heterogeneous_homDensity_sub_le
    (S : Finset (Sym2 V)) (U W : Sym2 V → Graphon α μ)
    (hS : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2) :
    |(∫ x : V → α, ∏ e ∈ S,
        (U e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
        ∂Measure.pi (fun _ => μ)) -
      (∫ x : V → α, ∏ e ∈ S,
        (W e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
        ∂Measure.pi (fun _ => μ))| ≤ ∑ e ∈ S, cutNormDiff (U e) (W e) := by
  rw [← integral_sub (heterogeneous_integrand_integrable S U hS)
    (heterogeneous_integrand_integrable S W hS)]
  simpa only [Finset.prod_empty, one_mul] using
    heterogeneous_weighted_homDensity_sub_le U W S ∅ U
      (Finset.disjoint_empty_left _) hS (by simp)

end Graphon
