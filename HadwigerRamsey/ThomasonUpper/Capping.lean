import HadwigerRamsey.ThomasonUpper.EdgeSelection
import HadwigerRamsey.ThomasonUpper.Stability

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- A uniform lower bound on every block's possible-edge denominator,
including the diagonal binomial denominator. -/
theorem blockCapacity_lower {n k : ℕ} (τ : Fin n → Fin k) {a : ℝ}
    (ha : 0 < a) (hn : 2 ≤ a*n)
    (hsize : ∀ i, a*n ≤ (classVertices τ i).card) (i j : Fin k) :
    a^2*(n : ℝ)^2/4 ≤ (blockCapacity τ i j : ℝ) := by
  have han : 0 ≤ a*(n : ℝ) := by positivity
  by_cases hij : i = j
  · subst j
    simp only [blockCapacity,eq_self_iff_true,ite_true]
    rw [Nat.cast_choose_two]
    have hs : (2 : ℝ) ≤ (classVertices τ i).card := hn.trans (hsize i)
    have hh := sq_le_sq₀ han (Nat.cast_nonneg _) |>.mpr (hsize i)
    nlinarith
  · simp only [blockCapacity,if_neg hij,Nat.cast_mul]
    have hh := mul_le_mul (hsize i) (hsize j) han (Nat.cast_nonneg _)
    nlinarith

/-- The capped spanning subgraph has uniformly close entropy, with an
explicit O(n^-2) error and the same class weights and diagonal convention
as the target theorem. -/
theorem exists_capped_subgraph_entropy {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 2 ≤ a*n) (hsize : ∀ i, a*n ≤ (classVertices τ i).card) :
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧
      (∀ i j, blockDensity H τ i j ≤ cappedDensity G τ ε i j ∧
        ε ≤ 1-blockDensity H τ i j) ∧
      |blockLambda τ (blockDensity H τ) - cappedLambda G τ ε| ≤
        4/(ε*a^2*(n : ℝ)^2) := by
  classical
  have hnR : (0 : ℝ) < n := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hnN : 0 < n := by exact_mod_cast hnR
  have hsizes : ∀ i, 2 ≤ (classVertices τ i).card := by
    intro i
    exact_mod_cast hn.trans (hsize i)
  obtain ⟨H,hHG,hH⟩ := exists_capped_subgraph G τ hε1 hsizes
  have hq : ∀ i j, ε ≤ 1-cappedDensity G τ ε i j ∧ 1-cappedDensity G τ ε i j ≤ 1 := by
    intro i j
    have hh := cappedDensity_bounds G τ hε1 i j
    constructor <;> linarith
  have hr : ∀ i j, ε ≤ 1-blockDensity H τ i j ∧ 1-blockDensity H τ i j ≤ 1 := by
    intro i j
    constructor
    · linarith [(hH i j).1,(hq i j).1]
    · linarith [blockDensity_nonneg H τ i j]
  have hd : ∀ i j, |(1-cappedDensity G τ ε i j)-(1-blockDensity H τ i j)| ≤
      4/(a^2*(n : ℝ)^2) := by
    intro i j
    have he : (1-cappedDensity G τ ε i j)-(1-blockDensity H τ i j) =
        blockDensity H τ i j-cappedDensity G τ ε i j := by ring
    rw [he]
    apply (hH i j).2.le.trans
    have hden : 0 < a^2*(n : ℝ)^2 := by positivity
    have hcap := blockCapacity_lower τ ha hn hsize i j
    have hcapPos : (0 : ℝ) < blockCapacity τ i j := (by positivity : 0 < a^2*(n : ℝ)^2/4).trans_le hcap
    apply (div_le_div_iff₀ hcapPos hden).mpr
    nlinarith
  have hl := lambda_stability (classMass τ) (classMass τ)
    (fun i j => 1-cappedDensity G τ ε i j) (fun i j => 1-blockDensity H τ i j)
    hε hε1 (classMass_nonneg τ) (classMass_nonneg τ)
    (sum_classMass hnN τ) (sum_classMass hnN τ) hq hr hd
  simp only [sub_self,abs_zero,sum_const_zero,mul_zero,add_zero] at hl
  change |cappedLambda G τ ε-blockLambda τ (blockDensity H τ)| ≤ _ at hl
  rw [abs_sub_comm] at hl
  refine ⟨H,hHG,fun i j => ⟨(hH i j).1,(hr i j).1⟩,?_⟩
  convert hl using 1
  ring

end HadwigerRamsey.ThomasonUpper
