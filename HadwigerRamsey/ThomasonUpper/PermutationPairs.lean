import HadwigerRamsey.ThomasonUpper.UniformPermutations

open scoped BigOperators Classical ENNReal
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- The ordered distinct-pair space has size s(s-1). -/
theorem card_ordered_distinct_pairs (A : Type*) [Fintype A] [DecidableEq A] :
    Fintype.card {z : A × A // z.1 ≠ z.2} = Fintype.card A*(Fintype.card A-1) := by
  rw [Fintype.card_subtype]
  have he : (univ.filter (fun z : A × A => z.1 ≠ z.2)) = (univ : Finset A).offDiag := by
    ext z
    simp
  rw [he,offDiag_card,card_univ]
  simp [Nat.mul_sub_left_distrib]

/-- With the first image fixed at x, the allowable second images are
exactly T with x removed. -/
theorem card_ordered_pair_event {A : Type*} [Fintype A] [DecidableEq A]
    (x : A) (T : Finset A) :
    Fintype.card ↑{z : {z : A × A // z.1 ≠ z.2} | z.val.1 = x ∧ z.val.2 ∈ T} =
      (T.erase x).card := by
  let e : {z : {z : A × A // z.1 ≠ z.2} // z.val.1 = x ∧ z.val.2 ∈ T} ≃ T.erase x :=
    { toFun := fun z => ⟨z.val.val.2,mem_erase.mpr ⟨by
          have hh := z.val.property
          rw [z.property.1] at hh
          exact hh.symm,z.property.2⟩⟩
      invFun := fun y => ⟨⟨(x,y.val),(mem_erase.mp y.property).1.symm⟩,
        rfl,(mem_erase.mp y.property).2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext z.property.1.symm rfl
      right_inv := by intro y; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

/-- The exact joint probability behind sampling a second part after the
first: 1/s for its first image, then |T minus x|/(s-1) for the second.
This is expressed without any conditional-probability convention. -/
theorem uniform_permutation_pair_event {A : Type*} [Fintype A] [DecidableEq A]
    (t u : A) (htu : t ≠ u) (x : A) (T : Finset A) :
    (PMF.uniformOfFintype (Equiv.Perm A)).toOuterMeasure
      {p | p t = x ∧ p u ∈ T} =
      ((T.erase x).card : ℝ≥0∞)/(Fintype.card A*(Fintype.card A-1) : ℕ) := by
  classical
  letI : Nonempty {z : A × A // z.1 ≠ z.2} := ⟨⟨(t,u),htu⟩⟩
  have he : {p : Equiv.Perm A | p t = x ∧ p u ∈ T} =
      (permutationPair t u htu) ⁻¹'
        {z : {z : A × A // z.1 ≠ z.2} | z.val.1 = x ∧ z.val.2 ∈ T} := rfl
  rw [he, ← PMF.toOuterMeasure_map_apply,uniform_permutation_pair,
    PMF.toOuterMeasure_uniformOfFintype_apply,card_ordered_pair_event,
    card_ordered_distinct_pairs]

end HadwigerRamsey.ThomasonUpper
