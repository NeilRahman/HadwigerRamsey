import ComponentTransfer.TransferConnected
import ComponentTransfer.TransferAtoms

open scoped Classical Topology ENNReal unitInterval
open MeasureTheory ProbabilityTheory Filter Set
open ComponentTransfer.Realization ComponentTransfer.Lifting

namespace ComponentTransfer.Transfer

/-- Encode countably many positive connected profile fibres by natural
numbers, reserving zero for the zero-degree remainder. -/
theorem exists_scalar_component_labels {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] [IsSeparable μ]
    (W : Graphon α μ) :
    ∃ label : α → ℕ, Measurable label ∧
      (∀ᵐ p ∂μ.prod μ, W.toAEEqFun p ≠ 0 →
        label p.1 = label p.2 ∧ label p.1 ≠ 0) ∧
      (∀ t : ℕ, t ≠ 0 → 0 < μ.real (label ⁻¹' {t}) →
        Connected (restrictGraphon W (label ⁻¹' {t}))) := by
  obtain ⟨code,C,hcode,hC,hpieces,hsupport⟩ := exists_component_profile W
  letI : Countable C := hC.to_subtype
  letI : Encodable C := Encodable.ofCountable C
  let enc : C → ℕ := Encodable.encode
  let F : Profile → ℕ := fun z => if hz : z ∈ C then enc ⟨z,hz⟩ + 1 else 0
  have hF : Measurable F := by
    exact (measurable_of_countable (fun z : C => enc z+1)).dite
      (measurable_const (a := (0 : ℕ))) hC.measurableSet
  let label : α → ℕ := F ∘ code
  have hfibre (z : C) : label ⁻¹' {enc z+1} = code ⁻¹' {z.val} := by
    ext x
    change F (code x) = enc z+1 ↔ code x = z.val
    constructor
    · intro hx
      by_cases hxC : code x ∈ C
      · have hh : enc ⟨code x,hxC⟩ = enc z := by
          simpa only [F, dif_pos hxC, Nat.add_right_cancel_iff] using hx
        exact congrArg Subtype.val (Encodable.encode_injective hh)
      · simp only [F, dif_neg hxC] at hx
        omega
    · intro hx
      simp only [F, hx, dif_pos z.property]
  refine ⟨label,hF.comp hcode,?_,?_⟩
  · filter_upwards [hsupport] with p hp
    intro hn
    obtain ⟨heq,hmem⟩ := hp hn
    constructor
    · exact congrArg F heq
    · change F (code p.1) ≠ 0
      simp only [F,dif_pos hmem,ne_eq,Nat.add_eq_zero_iff,one_ne_zero,and_false,not_false_eq_true]
  · intro t ht hpos
    have hne : (label ⁻¹' {t}).Nonempty := by
      by_contra h
      have hh : label ⁻¹' {t} = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [hh] at hpos
      simp at hpos
    obtain ⟨x,hx⟩ := hne
    have hx' : F (code x) = t := hx
    have hxC : code x ∈ C := by
      by_contra h
      simp only [F,dif_neg h] at hx'
      exact ht hx'.symm
    let z : C := ⟨code x,hxC⟩
    have htenc : t = enc z+1 := by simpa only [F,dif_pos hxC] using hx'.symm
    have heq : label ⁻¹' {t} = code ⁻¹' {z.val} := by rw [htenc,hfibre z]
    have hconn := (hpieces z.val z.property).2
    rw [← heq] at hconn
    exact hconn

/-- Every finite coloured graphon tuple has simultaneous countable
component labels. The label construction is performed separately on each
kernel; the underlying probability space is shared. -/
theorem exists_colored_components {r : ℕ} (W : Fin r → GraphonI) :
    Nonempty (ColoredComponents W) := by
  have h (c : Fin r) := exists_scalar_component_labels (volume : Measure I) (W c)
  choose label hlabel hsupport hconnected using h
  exact ⟨{
    label := label
    measurable_label := hlabel
    support := hsupport
    connected := fun c t ht hpos => hconnected c t ht hpos }⟩

end ComponentTransfer.Transfer
