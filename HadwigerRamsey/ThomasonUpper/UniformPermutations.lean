import Mathlib

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- A bijection transports the uniform probability mass function to the
uniform probability mass function on its codomain. -/
theorem uniform_map_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  classical
  ext b
  rw [PMF.map_apply]
  simp_rw [PMF.uniformOfFintype_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a ha
    have hab : b ≠ e a := by
      intro h
      apply ha
      exact e.injective (h.symm.trans (e.apply_symm_apply b).symm)
    simp [hab]

/-- The first coordinate of a uniformly sampled finite product is uniform. -/
theorem uniform_map_fst {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.fst = PMF.uniformOfFintype A := by
  classical
  ext a
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  simp [ENNReal.mul_inv, mul_left_comm, Fintype.card_ne_zero]
  rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := B)))
    (ENNReal.natCast_ne_top _), mul_one]

/-- A uniformly random permutation sends zero to a uniformly random point.
The proof reuses Mathlib's decomposition into that image and a permutation
of the remaining points. -/
theorem uniform_permutation_at_zero (n : ℕ) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin (n+1)))).map (fun p => p 0) =
      PMF.uniformOfFintype (Fin (n+1)) := by
  have hh := uniform_map_equiv (Equiv.Perm.decomposeFin (n := n))
  have hm := congrArg (fun p => p.map Prod.fst) hh
  rw [PMF.map_comp, uniform_map_fst] at hm
  have he : (Prod.fst ∘ (Equiv.Perm.decomposeFin (n := n))) = (fun p => p 0) := by
    funext p
    obtain ⟨z,hz⟩ := Equiv.Perm.decomposeFin.symm.surjective p
    subst p
    rcases z with ⟨x,p⟩
    simp
  rwa [he] at hm

/-- Every position of a uniform random permutation has the same uniform
marginal. Precomposition by a transposition exchanges that position with zero. -/
theorem uniform_permutation_at (n : ℕ) (t : Fin (n+1)) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin (n+1)))).map (fun p => p t) =
      PMF.uniformOfFintype (Fin (n+1)) := by
  let e : Equiv.Perm (Equiv.Perm (Fin (n+1))) :=
    { toFun := fun p => (Equiv.swap 0 t).trans p
      invFun := fun p => (Equiv.swap 0 t).trans p
      left_inv := by intro p; ext x; simp
      right_inv := by intro p; ext x; simp }
  have hh := uniform_map_equiv e
  have hm := congrArg (fun p => p.map (fun p => p 0)) hh
  rw [PMF.map_comp, uniform_permutation_at_zero] at hm
  simpa [e,Function.comp_def] using hm

/-- Uniform sampling descends through a map whose fibers are all
explicitly equivalent. This packages the finite symmetry argument. -/
theorem uniform_map_of_fiber_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A → B) (a0 : A)
    (E : ∀ b, {a // f a = b} ≃ {a // f a = f a0}) :
    (PMF.uniformOfFintype A).map f = PMF.uniformOfFintype B := by
  classical
  letI : Nonempty {a // f a = f a0} := ⟨⟨a0,rfl⟩⟩
  let d : A ≃ B × {a // f a = f a0} :=
    (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv E)
  have hh := uniform_map_equiv d
  have hm := congrArg (fun p => p.map Prod.fst) hh
  rw [PMF.map_comp,uniform_map_fst] at hm
  exact hm

/-- The images of two distinct positions under a random permutation. -/
def permutationPair {A : Type*} (t u : A) (htu : t ≠ u) (p : Equiv.Perm A) :
    {z : A × A // z.1 ≠ z.2} :=
  ⟨(p t,p u),fun h => htu (p.injective h)⟩

/-- All fibers of the ordered-pair evaluation map are equivalent,
by extending a bijection on the two designated points to a permutation. -/
theorem permutation_pair_fiber_equiv {A : Type*} [Fintype A] [DecidableEq A]
    (t u : A) (htu : t ≠ u) (b : {z : A × A // z.1 ≠ z.2}) :
    Nonempty ({p // permutationPair t u htu p = b} ≃
      {p // permutationPair t u htu p = permutationPair t u htu (Equiv.refl A)}) := by
  classical
  let f := permutationPair t u htu
  let v : Bool → A := fun c => if c then b.val.1 else b.val.2
  let w : Bool → A := fun c => if c then t else u
  have hv : Function.Injective v := by
    intro c d h
    cases c <;> cases d <;> simp_all [v,b.property,b.property.symm]
  have hw : Function.Injective w := by
    intro c d h
    cases c <;> cases d <;> simp_all [w,htu,htu.symm]
  obtain ⟨sigma,hsigma⟩ := Equiv.Perm.exists_extending_pair v w hv hw
  have hx : sigma b.val.1 = t := hsigma true
  have hy : sigma b.val.2 = u := hsigma false
  refine ⟨{
    toFun := fun p => ⟨p.val.trans sigma,?_⟩
    invFun := fun p => ⟨p.val.trans sigma.symm,?_⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · apply Subtype.ext
    have hp := congrArg Subtype.val p.property
    change (p.val t,p.val u) = b.val at hp
    change (sigma (p.val t),sigma (p.val u)) = (t,u)
    rw [show p.val t = b.val.1 from congrArg Prod.fst hp,
      show p.val u = b.val.2 from congrArg Prod.snd hp,hx,hy]
  · apply Subtype.ext
    have hp := congrArg Subtype.val p.property
    change (p.val t,p.val u) = (t,u) at hp
    change (sigma.symm (p.val t),sigma.symm (p.val u)) = b.val
    rw [show p.val t = t from congrArg Prod.fst hp,
      show p.val u = u from congrArg Prod.snd hp,← hx,← hy]
    simp
  · intro p
    apply Subtype.ext
    ext x
    exact sigma.symm_apply_apply _
  · intro p
    apply Subtype.ext
    ext x
    exact sigma.apply_symm_apply _

/-- Two distinct positions form a uniform ordered distinct pair. -/
theorem uniform_permutation_pair {A : Type*} [Fintype A] [DecidableEq A]
    (t u : A) (htu : t ≠ u) :
    (PMF.uniformOfFintype (Equiv.Perm A)).map (permutationPair t u htu) =
      @PMF.uniformOfFintype {z : A × A // z.1 ≠ z.2} _ ⟨⟨(t,u),htu⟩⟩ := by
  classical
  letI : Nonempty {z : A × A // z.1 ≠ z.2} := ⟨⟨(t,u),htu⟩⟩
  exact uniform_map_of_fiber_equiv (permutationPair t u htu) (Equiv.refl A)
    (fun b => Classical.choice (permutation_pair_fiber_equiv t u htu b))

/-- Applying the same balanced finite map independently in every
coordinate gives a uniform vector of images. -/
theorem uniform_pi_map_of_fiber_equiv {I A B : Type*}
    [Fintype I] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B) (a0 : A) (E : ∀ b, {a // f a = b} ≃ {a // f a = f a0}) :
    (PMF.uniformOfFintype (I → A)).map (fun p i => f (p i)) =
      PMF.uniformOfFintype (I → B) := by
  classical
  letI : Nonempty {a // f a = f a0} := ⟨⟨a0,rfl⟩⟩
  let d : A ≃ B × {a // f a = f a0} :=
    (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv E)
  let D : (I → A) ≃ (I → B) × (I → {a // f a = f a0}) :=
    (Equiv.piCongrRight (fun _ : I => d)).trans (Equiv.arrowProdEquivProdArrow I _ _)
  have hh := uniform_map_equiv D
  have hm := congrArg (fun p => p.map Prod.fst) hh
  rw [PMF.map_comp,uniform_map_fst] at hm
  exact hm

/-- Across all independently uniform block permutations, the ordered
pairs at two fixed positions form a uniform vector of distinct pairs. -/
theorem uniform_permutation_blocks_pair {I A : Type*} [Fintype I]
    [Fintype A] [DecidableEq A] (t u : A) (htu : t ≠ u) :
    (PMF.uniformOfFintype (I → Equiv.Perm A)).map
      (fun p i => permutationPair t u htu (p i)) =
      @PMF.uniformOfFintype (I → {z : A × A // z.1 ≠ z.2}) _
        ⟨fun _ => ⟨(t,u),htu⟩⟩ := by
  classical
  letI : Nonempty {z : A × A // z.1 ≠ z.2} := ⟨⟨(t,u),htu⟩⟩
  exact uniform_pi_map_of_fiber_equiv (permutationPair t u htu) (Equiv.refl A)
    (fun b => Classical.choice (permutation_pair_fiber_equiv t u htu b))

end HadwigerRamsey.ThomasonUpper
