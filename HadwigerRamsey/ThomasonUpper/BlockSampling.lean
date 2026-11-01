import HadwigerRamsey.ThomasonUpper.PermutationPairs

open scoped BigOperators Classical ENNReal
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Under the uniform law on a finite function space, the probability of
a rectangular event is the product of the coordinate probabilities. -/
theorem uniform_function_event {I A : Type*} [Fintype I] [Fintype A] [Nonempty A]
    (T : I → Set A) :
    (PMF.uniformOfFintype (I → A)).toOuterMeasure {f | ∀ i, f i ∈ T i} =
      ∏ i, (Nat.card (T i) : ℝ≥0∞)/Fintype.card A := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  let e : ↑{f : I → A | ∀ i, f i ∈ T i} ≃ (∀ i, T i) :=
    { toFun := fun f i => ⟨f.val i,f.property i⟩
      invFun := fun f => ⟨fun i => f i,fun i => (f i).property⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  rw [Fintype.card_congr e,Fintype.card_pi,Fintype.card_pi]
  simp only [Nat.cast_prod, Nat.card_eq_fintype_card]
  exact (ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.natCast_ne_top _)).symm

/-- Joint probabilities for two distinct parts, across all blocks.
The first chosen vertex in each block is fixed; the second can lie in T.
This is the exact finite calculation underlying A.1's conditioning step. -/
theorem uniform_block_pair_event {I A : Type*} [Fintype I]
    [Fintype A] [DecidableEq A] (t u : A) (htu : t ≠ u)
    (x : I → A) (T : I → Finset A) :
    (PMF.uniformOfFintype (I → Equiv.Perm A)).toOuterMeasure
      {p | ∀ i, p i t = x i ∧ p i u ∈ T i} =
      ∏ i, ((T i |>.erase (x i)).card : ℝ≥0∞)/
        (Fintype.card A*(Fintype.card A-1) : ℕ) := by
  classical
  letI : Nonempty {z : A × A // z.1 ≠ z.2} := ⟨⟨(t,u),htu⟩⟩
  let F := fun (p : I → Equiv.Perm A) i => permutationPair t u htu (p i)
  let E : I → Set {z : A × A // z.1 ≠ z.2} :=
    fun i => {z | z.val.1 = x i ∧ z.val.2 ∈ T i}
  have he : {p : I → Equiv.Perm A | ∀ i, p i t = x i ∧ p i u ∈ T i} =
      F ⁻¹' {z | ∀ i, z i ∈ E i} := rfl
  rw [he, ← PMF.toOuterMeasure_map_apply,
    show (PMF.uniformOfFintype (I → Equiv.Perm A)).map F = _ from
      uniform_permutation_blocks_pair t u htu,
    uniform_function_event E]
  apply prod_congr rfl
  intro i hi
  have hc : Nat.card (E i) = (T i |>.erase (x i)).card := by
    rw [Nat.card_eq_fintype_card]
    exact card_ordered_pair_event (x i) (T i)
  rw [hc,card_ordered_distinct_pairs]

/-- The first image in every block is a uniform vector of vertices. -/
theorem uniform_permutation_blocks_at {I A : Type*} [Fintype I]
    [Fintype A] [DecidableEq A] [Nonempty A] (t : A) :
    (PMF.uniformOfFintype (I → Equiv.Perm A)).map (fun p i => p i t) =
      PMF.uniformOfFintype (I → A) := by
  classical
  let E : ∀ b : A, {p : Equiv.Perm A // p t = b} ≃ {p : Equiv.Perm A // p t = t} :=
    fun b =>
      { toFun := fun p => ⟨p.val.trans (Equiv.swap b t),by
          change Equiv.swap b t (p.val t) = t
          rw [p.property]
          simp⟩
        invFun := fun p => ⟨p.val.trans (Equiv.swap b t),by
          change Equiv.swap b t (p.val t) = b
          rw [p.property]
          simp⟩
        left_inv := by intro p; apply Subtype.ext; ext x; simp
        right_inv := by intro p; apply Subtype.ext; ext x; simp }
  exact uniform_pi_map_of_fiber_equiv (fun p : Equiv.Perm A => p t) (Equiv.refl A) E

/-- The probability that the chosen vertex lies in a designated set in
every block is the product of the block proportions. -/
theorem uniform_block_event {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq A] [Nonempty A] (t : A) (T : I → Finset A) :
    (PMF.uniformOfFintype (I → Equiv.Perm A)).toOuterMeasure {p | ∀ i, p i t ∈ T i} =
      ∏ i, ((T i).card : ℝ≥0∞)/Fintype.card A := by
  have he : {p : I → Equiv.Perm A | ∀ i, p i t ∈ T i} =
      (fun p i => p i t) ⁻¹' {x : I → A | ∀ i, x i ∈ T i} := rfl
  rw [he,← PMF.toOuterMeasure_map_apply,uniform_permutation_blocks_at]
  simpa only [Finset.mem_coe,Finset.coe_sort_coe,Nat.card_eq_fintype_card,Fintype.card_coe] using
    (uniform_function_event (fun i => (T i : Set A)))

/-- The joint law in real numbers factors into the probability of the
fixed first vector and the remaining-vertex proportions for the second.
Thus the conditional sampling used in A.1 is verified by a finite identity. -/
theorem uniform_block_pair_event_real {I : Type*} [Fintype I] {s : ℕ}
    (t u : Fin s) (htu : t ≠ u) (x : I → Fin s) (T : I → Finset (Fin s))
    (hx : ∀ i, x i ∉ T i) :
    ((PMF.uniformOfFintype (I → Equiv.Perm (Fin s))).toOuterMeasure
      {p | ∀ i, p i t = x i ∧ p i u ∈ T i}).toReal =
      (1/(s : ℝ))^(Fintype.card I) * ∏ i, ((T i).card : ℝ)/((s : ℝ)-1) := by
  rw [uniform_block_pair_event t u htu x T,ENNReal.toReal_prod]
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,erase_eq_of_notMem (hx _),
    Fintype.card_fin,Nat.cast_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast]
  have hs : 1 ≤ s := by have := t.isLt; omega
  rw [Nat.cast_sub hs]
  calc
    _ = ∏ i, (1/(s : ℝ))*(((T i).card : ℝ)/((s : ℝ)-1)) := by
      apply prod_congr rfl
      intro i hi
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [prod_mul_distrib]; simp

end HadwigerRamsey.ThomasonUpper
