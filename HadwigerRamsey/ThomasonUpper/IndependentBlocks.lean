import Mathlib

open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory

namespace HadwigerRamsey.ThomasonUpper

/-- All coordinates in a finite block satisfy their designated event. -/
def allIn {I Ω : Type*} (A : I → Set Ω) (S : Finset I) : Set Ω := ⋂ i ∈ S, A i

theorem measurableSet_allIn {I Ω : Type*} [MeasurableSpace Ω]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (S : Finset I) :
    MeasurableSet (allIn A S) :=
  MeasurableSet.biInter (Set.to_countable _) (fun i _ => hA i)

/-- Disjoint vertex sets give independent all-label events. This is the
independence step for the internally disjoint paths in Lemma A.4. -/
theorem independent_allIn {I J Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hind : iIndepSet A μ) (S : J → Finset I)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepSet (fun j => allIn A (S j)) μ := by
  classical
  apply (iIndepSet_iff_meas_biInter (fun j => measurableSet_allIn A hA (S j))).mpr
  intro T
  have he : (⋂ j ∈ T, allIn A (S j)) = allIn A (T.biUnion S) := by
    ext ω
    simp only [allIn, Set.mem_iInter, mem_biUnion, forall_exists_index, and_imp]
    tauto
  rw [he, allIn, (iIndepSet_iff_meas_biInter hA).mp hind]
  rw [Finset.prod_biUnion (fun i _ j _ hij => hS hij)]
  apply prod_congr rfl
  intro j _
  exact ((iIndepSet_iff_meas_biInter hA).mp hind (S j)).symm

theorem probability_allIn {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hind : iIndepSet A μ) (S : Finset I) {r : ℝ}
    (hp : ∀ i ∈ S, μ.real (A i) = r) :
    μ.real (allIn A S) = r^S.card := by
  classical
  rw [measureReal_def, allIn, (iIndepSet_iff_meas_biInter hA).mp hind,
    ENNReal.toReal_prod]
  change (∏ i ∈ S, μ.real (A i)) = _
  simp only [prod_congr rfl hp, prod_const]

end HadwigerRamsey.ThomasonUpper
