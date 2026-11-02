import HadwigerRamsey.ControlledPartition.Basic
import HadwigerRamsey.ControlledPartition.Decomposition

open Finset
open scoped Classical

namespace HadwigerRamsey.ControlledPartition

theorem nbr_core_card {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Decomposition n) (v : Fin n) :
    (nbr G P.core v).card = ∑ S ∈ P.parts, (nbr G S v).card := by
  classical
  have he : nbr G P.core v = P.parts.biUnion (fun S => nbr G S v) := by
    ext w
    simp only [mem_nbr, Decomposition.mem_core, mem_biUnion]
    aesop
  rw [he, card_biUnion]
  intro S hS T hT hST
  exact (P.pairwise hS hT hST).mono
    (by intro w hw; exact ((mem_nbr _ _ _ _).mp hw).1)
    (by intro w hw; exact ((mem_nbr _ _ _ _).mp hw).1)

theorem parts_bound {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (P : Decomposition n) (hsize : ∀ S ∈ P.parts, 2*ε*n ≤ (S.card : ℝ)) :
    (P.parts.card : ℝ) * (2*ε) ≤ 1 ∧ (P.parts.card : ℝ) ≤ ε⁻¹ := by
  have hsum : (P.parts.card : ℝ) * (2*ε*n) ≤ n := by
    calc
      _ = ∑ _S ∈ P.parts, (2*ε*n) := by simp
      _ ≤ ∑ S ∈ P.parts, (S.card : ℝ) := sum_le_sum hsize
      _ ≤ n := by exact_mod_cast P.sum_card_parts_le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : (P.parts.card : ℝ) * (2*ε) ≤ 1 := by nlinarith only [hsum, hnR]
  refine ⟨hb, ?_⟩
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hε).mpr
  have hk : (0 : ℝ) ≤ P.parts.card := Nat.cast_nonneg _
  nlinarith only [hb, mul_nonneg hk hε.le]

theorem exists_many_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Decomposition n) {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hk : (P.parts.card : ℝ) ≤ ε⁻¹) (v : Fin n)
    (hv : η*n < ((nbr G P.core v).card : ℝ)) :
    ∃ S ∈ P.parts, ε*η*n < ((nbr G S v).card : ℝ) := by
  by_contra! hh
  have he := nbr_core_card G P v
  have hc : ((nbr G P.core v).card : ℝ) ≤ P.parts.card*(ε*η*n) := by
    rw [he, Nat.cast_sum]
    calc
      _ ≤ ∑ _S ∈ P.parts, ε*η*n := sum_le_sum hh
      _ = _ := by simp
  have hb : (P.parts.card : ℝ)*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hk hε.le
    simpa only [inv_mul_cancel₀ hε.ne'] using hh
  have hn : (0 : ℝ) ≤ η*n := mul_nonneg hη (Nat.cast_nonneg _)
  have hc' := mul_le_mul_of_nonneg_right hb hn
  nlinarith only [hv,hc,hc']

noncomputable def cutoff (ε η : ℝ) : ℝ :=
  min (ε^3 / ((⌊ε⁻¹⌋₊).factorial : ℝ))
    (ε*η / ((⌊ε⁻¹⌋₊).factorial : ℝ))

theorem cutoff_pos {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    0 < cutoff ε η := by
  unfold cutoff
  have hf : (0 : ℝ) < ((⌊ε⁻¹⌋₊).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  positivity

theorem cutoff_bounds {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    {k : ℕ} (hk : (k : ℝ) ≤ ε⁻¹) :
    (k.factorial : ℝ) * cutoff ε η ≤ ε^3 ∧
      (k.factorial : ℝ) * cutoff ε η ≤ ε*η := by
  have hkn : k ≤ ⌊ε⁻¹⌋₊ := (Nat.le_floor_iff (inv_pos.mpr hε).le).mpr hk
  have hfact : (k.factorial : ℝ) ≤ ((⌊ε⁻¹⌋₊).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hkn
  have hf : (0 : ℝ) < ((⌊ε⁻¹⌋₊).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h₁ : ((⌊ε⁻¹⌋₊).factorial : ℝ) * cutoff ε η ≤ ε^3 := by
    have hh : cutoff ε η ≤ ε^3 / ((⌊ε⁻¹⌋₊).factorial : ℝ) := min_le_left _ _
    nlinarith only [(le_div_iff₀ hf).mp hh]
  have h₂ : ((⌊ε⁻¹⌋₊).factorial : ℝ) * cutoff ε η ≤ ε*η := by
    have hh : cutoff ε η ≤ ε*η / ((⌊ε⁻¹⌋₊).factorial : ℝ) := min_le_right _ _
    nlinarith only [(le_div_iff₀ hf).mp hh]
  have hb := mul_le_mul_of_nonneg_right hfact (cutoff_pos hε hη).le
  exact ⟨hb.trans h₁, hb.trans h₂⟩

end HadwigerRamsey.ControlledPartition
