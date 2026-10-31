import HadwigerRamsey.OptApprox.Compactness

open scoped BigOperators
open Finset Real Set

namespace HadwigerRamsey
namespace OptApprox

/-- Finitely many possible dimensions have a common positive tolerance. -/
theorem bounded_dimensions (N : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℕ), k ≤ N → ∀ x ∈ Bad k ζ,
      ¬ ((∀ i, 1-δ ≤ prob x i+blue x i i+green x i i) ∧
         (∀ i j, i ≠ j → 1-δ ≤ blue x i j+green x i j)) := by
  classical
  choose d hd hspec using (fun j : Fin (N+1) => fixed_dimension j.val hζ)
  obtain ⟨j,hj,hmin⟩ := exists_min_image (univ : Finset (Fin (N+1))) d univ_nonempty
  refine ⟨d j,hd j,?_⟩
  intro k hk x hx ⟨hm,ho⟩
  let i : Fin (N+1) := ⟨k,by omega⟩
  have hle : d j ≤ d i := hmin i (mem_univ _)
  apply hspec i x hx
  exact ⟨fun r => le_trans (by linarith) (hm r),
    fun r s hrs => le_trans (by linarith) (ho r s hrs)⟩

end OptApprox

/-- Corollary `optapprox`, with closed bounds and an explicitly positive tolerance. -/
theorem optapprox (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 1/ζ →
      ∀ (α p : Fin k → ℝ) (qB qG : Fin k → Fin k → ℝ),
      (∀ i, 0 ≤ α i) → (∑ i, α i = 1) →
      (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1-ζ) →
      (∀ i j, 0 ≤ qB i j) → (∀ i j, qB i j ≤ 1-ζ) →
      (∀ i j, 0 ≤ qG i j) → (∀ i j, qG i j ≤ 1-ζ) →
      (∀ i j, qB i j = qB j i) → (∀ i j, qG i j = qG j i) →
      ¬ ((∀ i, 1-δ ≤ p i+qB i i+qG i i) ∧
         (∀ i j, i ≠ j → 1-δ ≤ qB i j+qG i j) ∧
         (∀ i, α i * sqrt (-log (1-p i)) ≤ beta-ζ) ∧
         sqrt (-(∑ i, ∑ j, α i*α j*log (1-qB i j))) ≤ beta-ζ ∧
         sqrt (-(∑ i, ∑ j, α i*α j*log (1-qG i j))) ≤ beta-ζ) := by
  obtain ⟨δ,hδ,htol⟩ := OptApprox.bounded_dimensions ⌊1/ζ⌋₊ hζ
  refine ⟨δ,hδ,?_⟩
  intro k _hk hk α p qB qG hα hs hp0 hp1 hB0 hB1 hG0 hG1 _hBsym _hGsym
  rintro ⟨hd,ho,hp,hB,hG⟩
  have hα1 (i : Fin k) : α i ≤ 1 := by
    rw [← hs]
    exact single_le_sum (fun j _ => hα j) (mem_univ i)
  let x : OptApprox.Config k ζ :=
    (fun i => ⟨α i,hα i,hα1 i⟩, fun i => ⟨p i,hp0 i,hp1 i⟩,
      fun i j => ⟨qB i j,hB0 i j,hB1 i j⟩, fun i j => ⟨qG i j,hG0 i j,hG1 i j⟩)
  have hx : x ∈ OptApprox.Bad k ζ := by
    refine ⟨hs,hp,?_,?_⟩
    · simpa only [OptApprox.weights,OptApprox.blue,x,Optimization.energy_eq_neg_sum] using hB
    · simpa only [OptApprox.weights,OptApprox.green,x,Optimization.energy_eq_neg_sum] using hG
  exact htol k (Nat.le_floor hk) x hx ⟨hd,ho⟩

end HadwigerRamsey
