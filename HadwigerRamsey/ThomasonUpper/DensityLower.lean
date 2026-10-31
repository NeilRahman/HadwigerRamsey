import HadwigerRamsey.ThomasonUpper.Density
import HadwigerRamsey.ThomasonUpper.Connectivity

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- The cut-based connectivity bound yields the degree-sum bound through
Mathlib's handshaking lemma. -/
theorem connectivity_mul_order_le_twice_edges {n : ℕ} (G : SimpleGraph (Fin n)) :
    (vertexConnectivity G : ℝ) * n ≤ 2 * (G.edgeFinset.card : ℝ) := by
  classical
  have hsum : (∑ _v : Fin n, vertexConnectivity G) ≤ ∑ v, G.degree v :=
    sum_le_sum fun v _ => vertexConnectivity_le_degree G v
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hr : (n : ℝ) * vertexConnectivity G ≤ 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum
  nlinarith

/-- Equation `eq:Lambda-main-lower`. No symmetry or density data are assumed:
they are computed from the actual graph and its partition. -/
theorem cappedLambda_lower {n k : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsizes : ∀ i, 2 ≤ (classVertices τ i).card)
    (hconn : ε * n ≤ (vertexConnectivity G : ℝ)) :
    ε * (1-ε) ≤ cappedLambda G τ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : ε * (n : ℝ)^2 ≤ 2 * (G.edgeFinset.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hconn hnR.le
    have hsum := connectivity_mul_order_le_twice_edges G
    nlinarith
  have hεden : ε ≤ 2 * (G.edgeFinset.card : ℝ) / (n : ℝ)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hnR)).mpr he
  calc
    ε * (1-ε) = (1-ε) * ε := mul_comm _ _
    _ ≤ (1-ε) * (2 * (G.edgeFinset.card : ℝ) / (n : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hεden (by linarith)
    _ ≤ (1-ε) * (∑ i, ∑ j, classMass τ i * classMass τ j * blockDensity G τ i j) :=
      mul_le_mul_of_nonneg_left (weighted_density_lower hn G τ hsizes) (by linarith)
    _ ≤ _ := cappedLambda_ge_weighted_density G τ hε hε1

/-- The theorem's minimum class mass makes every density well-defined once
the uniform order cutoff also ensures `ε n ≥ 2`. -/
theorem class_size_two {n k : ℕ} (hn : 0 < n) (τ : Fin n → Fin k)
    {ε : ℝ} (hmass : ∀ i, ε ≤ classMass τ i) (hsize : 2 ≤ ε * n) :
    ∀ i, 2 ≤ (classVertices τ i).card := by
  intro i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (le_div_iff₀ hnR).mp (hmass i)
  change ε * n ≤ ((classVertices τ i).card : ℝ) at h
  exact_mod_cast hsize.trans h

end HadwigerRamsey.ThomasonUpper
