import Mathlib
open scoped BigOperators
open Set MeasureTheory
namespace HadwigerRamsey.Existence

/-- Four high-probability properties hold simultaneously, also avoiding
an arbitrary finite family of null events. No independence between the
four graph properties is required. -/
theorem exists_four_good {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Fin 4 → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (Z : E → Set Ω) (hZ : ∀ e, MeasurableSet (Z e))
    {d : ℝ} (hd : 4*d < 1) (hp : ∀ i, 1-d ≤ μ.real (A i)) (hz : ∀ e, μ.real (Z e) = 0) :
    ∃ ω, (∀ i, ω ∈ A i) ∧ ∀ e, ω ∉ Z e := by
  let B := (⋃ i, (A i)ᶜ) ∪ ⋃ e, Z e
  have hB : MeasurableSet B := (MeasurableSet.iUnion (fun i => (hA i).compl)).union
    (MeasurableSet.iUnion hZ)
  have hzero : μ.real (⋃ e, Z e) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    exact (measureReal_iUnion_fintype_le Z).trans (by simp [hz])
  have hbad : μ.real B ≤ 4*d := by
    have hh := measureReal_iUnion_fintype_le (fun i => (A i)ᶜ) (μ := μ)
    have hs : (∑ i : Fin 4, μ.real (A i)ᶜ) ≤ 4*d := by
      calc
        _ ≤ ∑ _i : Fin 4, d := Finset.sum_le_sum (fun i _ => by
          have hc := measureReal_add_measureReal_compl (μ := μ) (hA i)
          rw [probReal_univ] at hc
          linarith only [hc,hp i])
        _ = _ := by simp
    have hh' := measureReal_union_le (⋃ i, (A i)ᶜ) (⋃ e, Z e) (μ := μ)
    change μ.real B ≤ _ at hh'
    linarith only [hh',hh,hs,hzero]
  have hc := measureReal_add_measureReal_compl (μ := μ) hB
  rw [probReal_univ] at hc
  obtain ⟨ω,hω⟩ := nonempty_of_measureReal_ne_zero (show μ.real Bᶜ ≠ 0 by linarith only [hc,hbad,hd])
  refine ⟨ω,?_,?_⟩
  · intro i
    by_contra hi
    exact hω (Or.inl (mem_iUnion.mpr ⟨i,hi⟩))
  · intro e he
    exact hω (Or.inr (mem_iUnion.mpr ⟨e,he⟩))
end HadwigerRamsey.Existence
