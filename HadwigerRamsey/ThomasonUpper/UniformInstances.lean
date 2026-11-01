import HadwigerRamsey.ThomasonUpper.BlockSampling

open scoped BigOperators Classical ENNReal
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Uniform finite probability does not depend on the chosen enumeration
of the sample space. This also avoids unfolding permutation enumerations
when using the sampling formulas in a concrete graph. -/
theorem uniform_fintype_irrel {A : Type*} (F F' : Fintype A) (N N' : Nonempty A) :
    @PMF.uniformOfFintype A F N = @PMF.uniformOfFintype A F' N' := by
  have h : F = F' := Subsingleton.elim _ _
  subst F'
  rfl

/-- The block-event formula with the sample-space enumeration explicit. -/
theorem uniform_block_event_of_fintype {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq A] [Nonempty A] (F : Fintype (I → Equiv.Perm A))
    (t : A) (T : I → Finset A) :
    (@PMF.uniformOfFintype (I → Equiv.Perm A) F inferInstance).toOuterMeasure
      {p | ∀ i, p i t ∈ T i} = ∏ i, ((T i).card : ℝ≥0∞)/Fintype.card A := by
  rw [uniform_fintype_irrel F (Pi.instFintype : Fintype (I → Equiv.Perm A)) inferInstance inferInstance]
  exact uniform_block_event t T

/-- The real paired-block formula with an explicit sample enumeration. -/
theorem uniform_block_pair_event_real_of_fintype {I : Type*} [Fintype I] {s : ℕ}
    (F : Fintype (I → Equiv.Perm (Fin s))) (t u : Fin s) (htu : t ≠ u)
    (x : I → Fin s) (T : I → Finset (Fin s)) (hx : ∀ i, x i ∉ T i) :
    ((@PMF.uniformOfFintype (I → Equiv.Perm (Fin s)) F inferInstance).toOuterMeasure
      {p | ∀ i, p i t = x i ∧ p i u ∈ T i}).toReal =
      (1/(s : ℝ))^(Fintype.card I) * ∏ i, ((T i).card : ℝ)/((s : ℝ)-1) := by
  rw [uniform_fintype_irrel F (Pi.instFintype : Fintype (I → Equiv.Perm (Fin s))) inferInstance inferInstance]
  exact uniform_block_pair_event_real t u htu x T hx

end HadwigerRamsey.ThomasonUpper
