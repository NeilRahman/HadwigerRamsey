import HadwigerRamsey4Col.LiftingRealization

open scoped Classical Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

set_option backward.isDefEq.respectTransparency false

namespace HadwigerRamsey4Col.Realization

/-- Null marking classes can be merged into one positive class, preserving
every prescribed positive class up to a null set. -/
theorem exists_positive_recode {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k m : ℕ}
    (mark : α → Fin m) (hmark : Measurable mark) (f : Fin k ↪ Fin m)
    (hk : 0 < k) (hpos : ∀ i, 0 < μ.real (mark ⁻¹' {f i})) :
    ∃ l : ℕ, ∃ mark' : α → Fin l, ∃ f' : Fin k ↪ Fin l,
      Measurable mark' ∧ (∀ j, 0 < μ.real (mark' ⁻¹' {j})) ∧
      ∀ i, mark' ⁻¹' {f' i} =ᵐ[μ] mark ⁻¹' {f i} := by
  let P : Set (Fin m) := {j | 0 < μ.real (mark ⁻¹' {j})}
  let j₀ : P := ⟨f ⟨0,hk⟩,hpos _⟩
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let recode : Fin m → Fin (Fintype.card P) := fun j =>
    if h : j ∈ P then e ⟨j,h⟩ else e j₀
  let mark' := recode ∘ mark
  let f' : Fin k ↪ Fin (Fintype.card P) :=
    ⟨fun i => e ⟨f i,hpos i⟩, by
      intro i j he
      exact f.injective (congrArg Subtype.val (e.injective he))⟩
  have hae : ∀ᵐ x ∂μ, mark x ∈ P := by
    have hnot (j : Fin m) : ∀ᵐ x ∂μ, mark x = j → j ∈ P := by
      by_cases hj : j ∈ P
      · exact Eventually.of_forall fun _ _ => hj
      · have hz : μ (mark ⁻¹' {j}) = 0 := by
          apply (measureReal_eq_zero_iff (μ := μ)).mp
          have hn := measureReal_nonneg (μ := μ) (s := mark ⁻¹' {j})
          exact le_antisymm (le_of_not_gt hj) hn
        have hx : ∀ᵐ x ∂μ, x ∉ mark ⁻¹' {j} := by
          rw [ae_iff]
          convert hz using 1
          congr 1
          ext x
          simp
        filter_upwards [hx] with x hx
        exact fun he => (hx he).elim
    have hh := Filter.eventually_all.mpr hnot
    filter_upwards [hh] with x hx
    exact hx (mark x) rfl
  have hfibre (j : P) : mark' ⁻¹' {e j} =ᵐ[μ] mark ⁻¹' {j.val} := by
    filter_upwards [hae] with x hx
    apply propext
    change recode (mark x) = e j ↔ mark x = j.val
    rw [show recode (mark x) = e ⟨mark x,hx⟩ by simp [recode,hx]]
    constructor
    · exact fun he => congrArg Subtype.val (e.injective he)
    · intro he
      exact congrArg e (Subtype.ext he)
  refine ⟨Fintype.card P,mark',f', ?_, ?_, ?_⟩
  · exact Measurable.of_discrete.comp hmark
  · intro j
    have h := hfibre (e.symm j)
    simp only [e.apply_symm_apply] at h
    rw [measureReal_def, measure_congr h]
    exact (e.symm j).property
  · intro i
    exact hfibre ⟨f i,hpos i⟩

/-- A full positive-measure partition extending disjoint positive sets,
with only null-set changes to the distinguished sets. -/
theorem exists_positive_partition_extension {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hpos : ∀ i, 0 < μ.real (A i)) :
    ∃ l : ℕ, ∃ mark : α → Fin l, ∃ f : Fin k ↪ Fin l,
      Measurable mark ∧ (∀ j, 0 < μ.real (mark ⁻¹' {j})) ∧
      ∀ i, mark ⁻¹' {f i} =ᵐ[μ] A i := by
  obtain ⟨mark,hmark,hfibre,_⟩ := exists_lifting_mark (Set.univ : Set α) MeasurableSet.univ
    A hA hdisjoint (fun _ => Set.subset_univ _)
  let f : Fin k ↪ Fin (k+2) := ⟨Fin.castAdd 2, fun _ _ he => Fin.ext (congrArg (fun z : Fin (k+2) => z.val) he)⟩
  have hactive (i : Fin k) : 0 < μ.real (mark ⁻¹' {f i}) := by
    change 0 < μ.real (mark ⁻¹' {Fin.castAdd 2 i})
    rw [hfibre]
    exact hpos i
  obtain ⟨l,mark',f',hm,hp,hae⟩ := exists_positive_recode μ mark hmark f hk hactive
  refine ⟨l,mark',f',hm,hp,fun i => ?_⟩
  have he : mark ⁻¹' {f i} = A i := by
    change mark ⁻¹' {Fin.castAdd 2 i} = A i
    exact hfibre i
  simpa only [he] using hae i

lemma rectIntegral_congr_ae_sets {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] (W : Graphon α μ)
    {A B C D : Set α} (hAC : A =ᵐ[μ] C) (hBD : B =ᵐ[μ] D) :
    W.toSymmKernel.rectIntegral A B = W.toSymmKernel.rectIntegral C D := by
  apply setIntegral_congr_set
  have hfst := (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hAC
  have hsnd := (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hBD
  filter_upwards [hfst,hsnd] with p hp hq
  exact propext (and_congr (Iff.of_eq hp) (Iff.of_eq hq))

end HadwigerRamsey4Col.Realization
