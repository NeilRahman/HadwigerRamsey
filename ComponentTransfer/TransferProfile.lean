import ComponentTransfer.TransferInvariant

open scoped Classical Topology ENNReal symmDiff
open MeasureTheory Filter Set

namespace ComponentTransfer.Transfer

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

abbrev Profile := ℕ → Bool

noncomputable def profile (S : ℕ → Set α) (x : α) : Profile :=
  fun n => if x ∈ S n then true else false

lemma profile_measurable {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n)) :
    Measurable (profile S) := by
  apply measurable_pi_iff.mpr
  intro n
  exact Measurable.ite (hS n) measurable_const measurable_const

lemma profile_mem_iff {S : ℕ → Set α} {x : α} {z : Profile}
    (hx : profile S x = z) (n : ℕ) : x ∈ S n ↔ z n = true := by
  have hh := congrFun hx n
  by_cases hm : x ∈ S n <;> simp [profile,hm] at hh ⊢ <;> simp [← hh]

lemma profile_fibre_invariant {W : Graphon α μ} {S : ℕ → Set α}
    (hS : ∀ n, Invariant W (S n)) (z : Profile) :
    Invariant W (profile S ⁻¹' {z}) := by
  refine ⟨(profile_measurable (fun n => (hS n).1)) (measurableSet_singleton z),?_⟩
  have hh : ∀ᵐ p ∂μ.prod μ, ∀ n, W.toAEEqFun p ≠ 0 →
      (p.1 ∈ S n ↔ p.2 ∈ S n) := ae_all_iff.mpr (fun n => (hS n).2)
  filter_upwards [hh] with p hp
  intro hn
  have he : profile S p.1 = profile S p.2 := by
    funext n
    simp only [profile]
    rw [if_congr (hp n hn) rfl rfl]
  change profile S p.1 = z ↔ profile S p.2 = z
  rw [he]

lemma profile_fibre_atomic {W : Graphon α μ} {S : ℕ → Set α}
    (hS : ∀ n, Invariant W (S n))
    (hdense : ∀ T : Set α, Invariant W T → ∀ ε > 0, ∃ n, μ.real (T ∆ S n) < ε)
    (z : Profile) (T : Set α) (hT : Invariant W T) :
    μ.real ((profile S ⁻¹' {z}) ∩ T) = 0 ∨
      μ.real ((profile S ⁻¹' {z}) \ T) = 0 := by
  let B := profile S ⁻¹' {z}
  by_contra hnot
  push_neg at hnot
  have hleft : 0 < μ.real (B ∩ T) := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hnot.1)
  have hright : 0 < μ.real (B \ T) := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hnot.2)
  let ε := min (μ.real (B ∩ T)) (μ.real (B \ T))
  have hε : 0 < ε := lt_min hleft hright
  obtain ⟨n,hn⟩ := hdense T hT ε hε
  cases hz : z n with
  | false =>
    have hsub : B ∩ T ⊆ T ∆ S n := by
      intro x hx
      have hnot : x ∉ S n := by
        intro hm
        have hh := (profile_mem_iff hx.1 n).mp hm
        simp [hz] at hh
      exact Or.inl ⟨hx.2,hnot⟩
    have hle := measureReal_mono hsub (measure_ne_top μ _)
    have hsmall : ε ≤ μ.real (B ∩ T) := min_le_left _ _
    linarith
  | true =>
    have hsub : B \ T ⊆ T ∆ S n := by
      intro x hx
      have hm : x ∈ S n := (profile_mem_iff hx.1 n).mpr hz
      exact Or.inr ⟨hm,hx.2⟩
    have hle := measureReal_mono hsub (measure_ne_top μ _)
    have hsmall : ε ≤ μ.real (B \ T) := min_le_right _ _
    linarith

/-- Only countably many membership profiles have positive measure. -/
lemma countable_positive_profiles {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n)) :
    Set.Countable {z : Profile | 0 < μ (profile S ⁻¹' {z})} :=
  Measure.countable_meas_level_set_pos (profile_measurable hS)

/-- Almost every positive kernel edge belongs to a common positive profile
fibre. The union of the null fibres contributes no edges. -/
lemma profile_support {W : Graphon α μ} {S : ℕ → Set α}
    (hS : ∀ n, Invariant W (S n)) :
    ∀ᵐ p ∂μ.prod μ, W.toAEEqFun p ≠ 0 →
      profile S p.1 = profile S p.2 ∧ 0 < μ (profile S ⁻¹' {profile S p.1}) := by
  let C : Set Profile := {z | 0 < μ (profile S ⁻¹' {z})}
  have hCcount : C.Countable := countable_positive_profiles (fun n => (hS n).1)
  have hCmeas : MeasurableSet C := hCcount.measurableSet
  have hpmeas := profile_measurable (fun n => (hS n).1)
  let E : Set (α × α) := {p | profile S p.1 = profile S p.2 ∧ profile S p.1 ∉ C}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun (hpmeas.comp measurable_fst) (hpmeas.comp measurable_snd)).inter
      ((hpmeas.comp measurable_fst) hCmeas).compl
  have hnull : (μ.prod μ) E = 0 := by
    rw [Measure.prod_apply hE]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Eventually.of_forall
    intro x
    change μ (Prod.mk x ⁻¹' E) = 0
    by_cases hx : profile S x ∈ C
    · have he : (Prod.mk x ⁻¹' E) = ∅ := by ext y; simp [E,hx]
      simp [he]
    · have he : (Prod.mk x ⁻¹' E) = profile S ⁻¹' {profile S x} := by
        ext y
        simp [E,hx,eq_comm]
      rw [he]
      exact le_antisymm (le_of_not_gt hx) bot_le
  have hnotE : ∀ᵐ p ∂μ.prod μ, p ∉ E := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  have hpreserve : ∀ᵐ p ∂μ.prod μ, ∀ n, W.toAEEqFun p ≠ 0 →
      (p.1 ∈ S n ↔ p.2 ∈ S n) := ae_all_iff.mpr (fun n => (hS n).2)
  filter_upwards [hnotE,hpreserve] with p hp hpS
  intro hn
  have he : profile S p.1 = profile S p.2 := by
    funext n
    simp only [profile]
    rw [if_congr (hpS n hn) rfl rfl]
  refine ⟨he,?_⟩
  by_contra hzero
  exact hp ⟨he,hzero⟩

end ComponentTransfer.Transfer
