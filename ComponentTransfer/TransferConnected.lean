import ComponentTransfer.TransferProfile

open scoped Classical Topology ENNReal symmDiff
open MeasureTheory ProbabilityTheory Filter Set
open ComponentTransfer.Realization

namespace ComponentTransfer.Transfer

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

lemma ae_zero_on_rectangle (W : Graphon α μ) (A B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hz : W.toSymmKernel.rectIntegral A B = 0) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ A → p.2 ∈ B → W.toAEEqFun p = 0 := by
  have hn : ∀ᵐ p ∂(μ.prod μ).restrict (A ×ˢ B), 0 ≤ W.toAEEqFun p :=
    (ae_restrict_of_ae W.ae_mem_Icc).mono (fun _ hp => hp.1)
  have heq : W.toAEEqFun =ᵐ[(μ.prod μ).restrict (A ×ˢ B)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hn (SymmKernel.graphon_integrable W).integrableOn).mp hz
  change (∀ᵐ p ∂(μ.prod μ).restrict (A ×ˢ B), W.toAEEqFun p = 0) at heq
  rw [ae_restrict_iff' (hA.prod hB)] at heq
  filter_upwards [heq] with p hp h₁ h₂
  exact hp ⟨h₁,h₂⟩

lemma Invariant.inter_of_rectangle_zero {W : Graphon α μ} {B : Set α}
    (hB : Invariant W B) (A : Set α) (hA : MeasurableSet A)
    (hz : W.toSymmKernel.rectIntegral (A ∩ B) (Aᶜ ∩ B) = 0) :
    Invariant W (A ∩ B) := by
  apply invariant_of_rectIntegral_zero W (A ∩ B) (hA.inter hB.1)
  apply setIntegral_eq_zero_of_ae_eq_zero
  have hzero := ae_zero_on_rectangle W (A ∩ B) (Aᶜ ∩ B)
    (hA.inter hB.1) (hA.compl.inter hB.1) hz
  filter_upwards [hB.2,hzero] with p hB hz hp
  by_cases hn : W.toAEEqFun p = 0
  · exact hn
  have h₂B : p.2 ∈ B := (hB hn).mp hp.1.2
  have h₂notA : p.2 ∉ A := by
    intro h₂A
    exact hp.2 ⟨h₂A,h₂B⟩
  exact hz hp.1 ⟨h₂notA,h₂B⟩

/-- Positive fibres of a dense invariant membership profile are connected. -/
theorem profile_fibre_connected {W : Graphon α μ} {S : ℕ → Set α}
    (hS : ∀ n, Invariant W (S n))
    (hdense : ∀ T : Set α, Invariant W T → ∀ ε > 0, ∃ n, μ.real (T ∆ S n) < ε)
    (z : Profile) (hpos : 0 < μ (profile S ⁻¹' {z})) :
    Lifting.Connected (restrictGraphon W (profile S ⁻¹' {z})) := by
  let B := profile S ⁻¹' {z}
  have hB : Invariant W B := profile_fibre_invariant hS z
  have hBr : 0 < μ.real B := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ B)
  letI : IsProbabilityMeasure (cond μ B) := cond_isProbabilityMeasure hpos.ne'
  intro A hA hlow hhigh
  have hcond (D : Set α) : (cond μ B).real D = μ.real (B ∩ D)/μ.real B := by
    simp only [measureReal_def,cond_apply hB.1,ENNReal.toReal_mul,ENNReal.toReal_inv]
    ring
  have hleft : 0 < μ.real (B ∩ A) := by
    rw [hcond] at hlow
    rcases div_pos_iff.mp hlow with h | h
    · exact h.1
    · linarith [h.2]
  have hright : 0 < μ.real (B ∩ Aᶜ) := by
    have hc : 0 < (cond μ B).real Aᶜ := by
      rw [probReal_compl_eq_one_sub hA]
      linarith
    rw [hcond] at hc
    rcases div_pos_iff.mp hc with h | h
    · exact h.1
    · linarith [h.2]
  by_contra! hnot
  have hnonneg : 0 ≤ (restrictGraphon W B).toSymmKernel.rectIntegral A Aᶜ := by
    apply integral_nonneg_of_ae
    exact (ae_restrict_of_ae (restrictGraphon W B).ae_mem_Icc).mono (fun _ h => h.1)
  have hz : (restrictGraphon W B).toSymmKernel.rectIntegral A Aᶜ = 0 := le_antisymm hnot hnonneg
  rw [restrictGraphon_rectIntegral W B A Aᶜ hA hA.compl] at hz
  have hzraw : W.toSymmKernel.rectIntegral (A ∩ B) (Aᶜ ∩ B) = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 hBr.ne')
  have hT := hB.inter_of_rectangle_zero A hA hzraw
  have hatom := profile_fibre_atomic hS hdense z (A ∩ B) hT
  have h₁ : B ∩ (A ∩ B) = B ∩ A := by ext x; simp; tauto
  have h₂ : B \ (A ∩ B) = B ∩ Aᶜ := by ext x; simp
  change μ.real (B ∩ (A ∩ B)) = 0 ∨ μ.real (B \ (A ∩ B)) = 0 at hatom
  rw [h₁,h₂] at hatom
  rcases hatom with h | h <;> linarith

/-- A scalar graphon has countably many positive connected invariant
pieces, and every nonzero kernel edge is contained in one of these pieces. -/
theorem exists_component_profile (W : Graphon α μ) [IsSeparable μ] :
    ∃ (code : α → Profile) (C : Set Profile), Measurable code ∧ C.Countable ∧
      (∀ z ∈ C, 0 < μ (code ⁻¹' {z}) ∧
        Lifting.Connected (restrictGraphon W (code ⁻¹' {z}))) ∧
      (∀ᵐ p ∂μ.prod μ, W.toAEEqFun p ≠ 0 →
        code p.1 = code p.2 ∧ code p.1 ∈ C) := by
  obtain ⟨S,hS,hdense⟩ := exists_dense_invariant_sequence W
  let C : Set Profile := {z | 0 < μ (profile S ⁻¹' {z})}
  refine ⟨profile S,C,profile_measurable (fun n => (hS n).1),
    countable_positive_profiles (fun n => (hS n).1),?_,profile_support hS⟩
  intro z hz
  exact ⟨hz,profile_fibre_connected hS hdense z hz⟩

end ComponentTransfer.Transfer
