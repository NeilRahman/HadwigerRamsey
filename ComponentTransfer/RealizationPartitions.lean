import ComponentTransfer.RealizationDensities
import ComponentTransfer.RealizationRestriction

open scoped Classical Topology
open MeasureTheory Set Filter

namespace ComponentTransfer.Realization

/-- A finite measurable partition can be encoded by a measurable label map,
with exactly the original sets as fibres. -/
theorem exists_partition_mark {α : Type*} [MeasurableSpace α] {k : ℕ}
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : (⋃ i, A i) = Set.univ) :
    ∃ mark : α → Fin k, Measurable mark ∧ ∀ i, mark ⁻¹' {i} = A i := by
  have hex (x : α) : ∃ i, x ∈ A i := by
    apply Set.mem_iUnion.mp
    rw [hcover]
    trivial
  let mark : α → Fin k := fun x => (hex x).choose
  have hmem (x : α) : x ∈ A (mark x) := (hex x).choose_spec
  have hfibre (i : Fin k) : mark ⁻¹' {i} = A i := by
    ext x
    constructor
    · intro hx
      have he : mark x = i := hx
      exact he ▸ hmem x
    · intro hx
      change mark x = i
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint hne) (hmem x) hx
  refine ⟨mark, ?_, hfibre⟩
  apply measurable_to_countable'
  intro i
  rw [hfibre i]
  exact hA i

lemma partition_mark_union {α : Type*} {k : ℕ}
    (A : Fin k → Set α) (mark : α → Fin k)
    (hfibre : ∀ i, mark ⁻¹' {i} = A i) (J : Finset (Fin k)) :
    mark ⁻¹' (J : Set (Fin k)) = ⋃ i ∈ J, A i := by
  ext x
  simp only [Set.mem_preimage, Finset.mem_coe, Set.mem_iUnion]
  constructor
  · intro hx
    exact ⟨mark x, hx, by rw [← hfibre]; rfl⟩
  · rintro ⟨i, hi, hxi⟩
    rw [← hfibre] at hxi
    have he : mark x = i := hxi
    rwa [he]

lemma partition_mark_union_pos {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {k : ℕ}
    (mark : α → Fin k) (hpos : ∀ i, 0 < μ.real (mark ⁻¹' {i}))
    (J : Finset (Fin k)) (hJ : J.Nonempty) :
    0 < μ.real (mark ⁻¹' (J : Set (Fin k))) := by
  obtain ⟨i, hi⟩ := hJ
  apply (hpos i).trans_le
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  have he : mark x = i := hx
  simpa [he] using hi

end ComponentTransfer.Realization
