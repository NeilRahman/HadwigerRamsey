import HadwigerRamsey.ThomasonUpper.Definitions

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

theorem internalDensity_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) : 0 ≤ internalDensity G S := by
  classical
  unfold internalDensity
  positivity

theorem internalDensity_le_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) : internalDensity G S ≤ 1 := by
  classical
  have h := (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
  have hc : Fintype.card (S : Set V) = S.card :=
    Fintype.card_of_subtype S (by intro x; rfl)
  rw [hc] at h
  exact div_le_one_of_le₀ (by exact_mod_cast h) (by positivity)

/-- The directed incidence count within a class is twice its undirected
edge count. This relates Mathlib's density convention to the manuscript's. -/
theorem card_internal_interedges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    (G.interedges S S).card = 2 * (G.induce (S : Set V)).edgeFinset.card := by
  classical
  rw [SimpleGraph.two_mul_card_edgeFinset]
  symm
  apply Finset.card_bij (fun e _ => (e.1.val, e.2.val))
  · intro e he
    exact G.mem_interedges_iff.mpr ⟨e.1.property, e.2.property, (mem_filter.mp he).2⟩
  · intro e _ f _ hef
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hef))
      (Subtype.ext (congrArg Prod.snd hef))
  · intro e he
    obtain ⟨hu, hv, huv⟩ := G.mem_interedges_iff.mp he
    exact ⟨(⟨e.1, hu⟩, ⟨e.2, hv⟩), mem_filter.mpr ⟨mem_univ _, huv⟩, rfl⟩

theorem edgeDensity_le_internalDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : 2 ≤ S.card) :
    (G.edgeDensity S S : ℝ) ≤ internalDensity G S := by
  classical
  have hSR : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
  have hpos : (0 : ℝ) < S.card := by linarith
  have hchoose : (0 : ℝ) < S.card.choose 2 := by
    exact_mod_cast Nat.choose_pos hS
  have hE : (0 : ℝ) ≤ (G.induce (S : Set V)).edgeFinset.card := by positivity
  simp only [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    card_internal_interedges, Nat.cast_mul, Nat.cast_ofNat, internalDensity]
  apply (div_le_div_iff₀ (mul_pos hpos hpos) hchoose).mpr
  rw [Nat.cast_choose_two]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = ((G.induce (S : Set V)).edgeFinset.card : ℝ) *
        ((S.card : ℝ) * S.card) - ((G.induce (S : Set V)).edgeFinset.card : ℝ) *
        S.card := by ring
    _ ≤ _ := sub_le_self _ (by positivity)

theorem blockDensity_nonneg {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) : 0 ≤ blockDensity G τ i j := by
  classical
  unfold blockDensity
  split
  · exact internalDensity_nonneg _ _
  · exact_mod_cast G.edgeDensity_nonneg _ _

theorem blockDensity_le_one {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) : blockDensity G τ i j ≤ 1 := by
  classical
  unfold blockDensity
  split
  · exact internalDensity_le_one _ _
  · exact_mod_cast G.edgeDensity_le_one _ _

theorem blockDensity_symm {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) : blockDensity G τ i j = blockDensity G τ j i := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  · simp only [blockDensity, if_neg hij, if_neg (Ne.symm hij)]
    rw [G.edgeDensity_comm]

/-- The blocks exhaust the ordered incidences, including both orientations
of every internal or external edge. -/
theorem sum_card_block_interedges {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) :
    (∑ i, ∑ j, (G.interedges (classVertices τ i) (classVertices τ j)).card) =
      2 * G.edgeFinset.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := G.interedges univ univ) (t := univ)
    (f := fun e => (τ e.1, τ e.2)) (by intro e _; exact mem_univ _)
  rw [Fintype.sum_prod_type] at h
  have hcounts : (∑ i, ∑ j, (G.interedges (classVertices τ i) (classVertices τ j)).card) =
      ∑ i, ∑ j, ((G.interedges univ univ).filter
        fun e => (τ e.1, τ e.2) = (i, j)).card := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    congr 1
    ext e
    simp only [SimpleGraph.mem_interedges_iff, classVertices, mem_filter,
      mem_univ, true_and, Prod.mk.injEq]
    tauto
  rw [hcounts, ← h, G.interedges_def]
  simpa using G.two_mul_card_edgeFinset.symm

/-- Correcting the diagonal normalization can only increase the globally
weighted density relative to the ordinary directed edge count. -/
theorem weighted_density_lower {n k : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (τ : Fin n → Fin k)
    (hsizes : ∀ i, 2 ≤ (classVertices τ i).card) :
    2 * (G.edgeFinset.card : ℝ) / (n : ℝ)^2 ≤
      ∑ i, ∑ j, classMass τ i * classMass τ j * blockDensity G τ i j := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm : ∀ i j,
      ((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ) / (n : ℝ)^2 ≤
        classMass τ i * classMass τ j * blockDensity G τ i j := by
    intro i j
    have hi : ((classVertices τ i).card : ℝ) ≠ 0 := by
      have := hsizes i; exact_mod_cast (by omega : (classVertices τ i).card ≠ 0)
    have hj : ((classVertices τ j).card : ℝ) ≠ 0 := by
      have := hsizes j; exact_mod_cast (by omega : (classVertices τ j).card ≠ 0)
    have hden : classMass τ i * classMass τ j *
        (G.edgeDensity (classVertices τ i) (classVertices τ j) : ℝ) =
        ((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ) / (n : ℝ)^2 := by
      simp only [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
      change ((classVertices τ i).card : ℝ) / n * (((classVertices τ j).card : ℝ) / n) *
        (_ / (((classVertices τ i).card : ℝ) * (classVertices τ j).card)) = _
      field_simp
    rw [← hden]
    apply mul_le_mul_of_nonneg_left _ (by unfold classMass; positivity)
    by_cases hij : i = j
    · subst j
      simpa [blockDensity] using
        edgeDensity_le_internalDensity G (classVertices τ i) (hsizes i)
    · simp only [blockDensity, if_neg hij, le_refl]
  calc
    _ = ∑ i, ∑ j,
        ((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ) / (n : ℝ)^2 := by
      simp only [← sum_div, ← Nat.cast_sum]
      rw [sum_card_block_interedges, Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ _ := sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j

theorem classMass_nonneg {n k : ℕ} (τ : Fin n → Fin k) (i : Fin k) :
    0 ≤ classMass τ i := by unfold classMass; positivity

theorem sum_classMass {n k : ℕ} (hn : 0 < n) (τ : Fin n → Fin k) :
    ∑ i, classMass τ i = 1 := by
  have h := sum_pullback τ (fun _ => 1)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  simp only [classMass, ← Finset.sum_div]
  rw [← h, div_self (by exact_mod_cast hn.ne')]

theorem cappedDensity_bounds {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} (hε : ε ≤ 1) (i j : Fin k) :
    0 ≤ cappedDensity G τ ε i j ∧ cappedDensity G τ ε i j ≤ 1 - ε := by
  exact ⟨le_min (blockDensity_nonneg _ _ _ _) (by linarith), min_le_right _ _⟩

theorem cappedDensity_symm {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (ε : ℝ) (i j : Fin k) :
    cappedDensity G τ ε i j = cappedDensity G τ ε j i := by
  simp only [cappedDensity, blockDensity_symm G τ i j]

/-- Capping retains at least a factor `1-ε` of each density. -/
theorem cappedDensity_ge {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (i j : Fin k) :
    (1-ε) * blockDensity G τ i j ≤ cappedDensity G τ ε i j := by
  apply le_min
  · nlinarith [blockDensity_nonneg G τ i j]
  · nlinarith [blockDensity_le_one G τ i j]

theorem cappedLambda_ge_weighted_density {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1-ε) * (∑ i, ∑ j, classMass τ i * classMass τ j * blockDensity G τ i j) ≤
      cappedLambda G τ ε := by
  unfold cappedLambda blockLambda
  simp only [mul_sum]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  have hpos : 0 < 1 - cappedDensity G τ ε i j := by
    have := (cappedDensity_bounds G τ hε1 i j).2
    linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hp : (1-ε) * blockDensity G τ i j ≤ -log (1-cappedDensity G τ ε i j) := by
    have := cappedDensity_ge G τ hε.le hε1 i j
    linarith
  have hmass : 0 ≤ classMass τ i * classMass τ j := by unfold classMass; positivity
  nlinarith [mul_le_mul_of_nonneg_left hp hmass]

theorem cappedLambda_nonneg {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ cappedLambda G τ ε := by
  unfold cappedLambda blockLambda
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (classMass_nonneg _ _) (classMass_nonneg _ _))
    (log_weight_bounds hε (cappedDensity_bounds G τ hε1 i j).1
      (cappedDensity_bounds G τ hε1 i j).2).1

/-- Equation `eq:Lambda-main-upper`, uniformly in the graph and partition. -/
theorem cappedLambda_le {n k : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    cappedLambda G τ ε ≤ log (1 / ε) := by
  have hsum := sum_classMass hn τ
  calc
    cappedLambda G τ ε ≤ ∑ i, ∑ j, classMass τ i * classMass τ j * (-log ε) := by
      unfold cappedLambda blockLambda
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (log_weight_bounds hε (cappedDensity_bounds G τ hε1 i j).1
          (cappedDensity_bounds G τ hε1 i j).2).2
        (mul_nonneg (classMass_nonneg _ _) (classMass_nonneg _ _))
    _ = -log ε := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]
    _ = log (1 / ε) := by rw [one_div, log_inv]

/-- The multiplicative-to-additive accuracy conversion at the end of the
appendix does not move the error term inside the square root. -/
theorem additive_accuracy {Λ B ε δ : ℝ} (hB : 0 < B) (hΛ : Λ ≤ B)
    (hε : 0 ≤ ε) (hδ : δ = ε / sqrt B) :
    sqrt Λ - ε ≤ (1 - δ) * sqrt Λ := by
  have hroot := Real.sqrt_le_sqrt hΛ
  have hden := Real.sqrt_pos.mpr hB
  have hprod : δ * sqrt Λ ≤ ε := by
    rw [hδ]
    calc
      ε / sqrt B * sqrt Λ ≤ ε / sqrt B * sqrt B :=
        mul_le_mul_of_nonneg_left hroot (div_nonneg hε hden.le)
      _ = ε := div_mul_cancel₀ _ hden.ne'
  nlinarith

end HadwigerRamsey.ThomasonUpper
