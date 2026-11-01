import HadwigerRamsey.ThomasonUpper.BlockMaxProducts

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- The weight rho from the complete-equipartition argument. -/
noncomputable def nonneighborWeight {n k : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (ell : Fin k → ℕ) (L : ℕ) (t : ℝ) (u : Fin n) : ℝ :=
  ∏ j, (min 1 (nonneighborFraction G classes j u+t))^((ell j : ℝ)/L)

/-- Sorted blocks for the actual graph weights, carrying all the class
logarithmic-mean estimates needed for the product of block maxima. -/
theorem exists_sorted_nonneighbor_blocks {n k s L : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (ell : Fin k → ℕ)
    (hs : 2 ≤ s) (hell : ∀ i, 1 ≤ ell i)
    (hcard : ∀ i, (classVertices classes i).card = s*ell i)
    (hL : 0 < L) (hsum : ∑ i, ell i = L) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i,
    ∃ theta : ∀ i, Fin (ell i) → ℝ,
      (∀ i a, t ≤ theta i a ∧ theta i a ≤ 1) ∧
      (∀ i a x, nonneighborWeight G classes ell L t (e i (a,x)) ≤ theta i a) ∧
      (∀ i a (ha : a.val+1 < ell i) x,
        theta i a ≤ nonneighborWeight G classes ell L t (e i (⟨a.val+1,ha⟩,x))) ∧
      (∀ i, (∑ a, ∑ x, log (nonneighborWeight G classes ell L t (e i (a,x)))) ≤
        (s : ℝ)*(ell i)*(∑ j, ((ell j : ℝ)/L)*
          log (min 1 (1-blockDensity G classes i j+t)))) := by
  have hspos : 0 < s := by omega
  have hsizes : ∀ i, 2 ≤ (classVertices classes i).card := by
    intro i
    rw [hcard]
    nlinarith [hell i]
  let rho := nonneighborWeight G classes ell L t
  have hrho : ∀ u, t ≤ rho u ∧ rho u ≤ 1 :=
    fun u => rho_bounds G classes ell L hL hsum ht ht1 u
  have hexists := fun i => exists_sorted_blocks (classVertices classes i) rho hspos
    ((hcard i).trans (Nat.mul_comm s (ell i))) (fun u _ => hrho u)
  choose e theta htheta hmax hshift using hexists
  refine ⟨e,theta,htheta,hmax,hshift,?_⟩
  intro i
  have heq : (∑ a, ∑ x, log (rho (e i (a,x)))) =
      ∑ u ∈ classVertices classes i, log (rho u) := by
    calc
      _ = ∑ z : Fin (ell i) × Fin s, log (rho (e i z)) :=
        (Fintype.sum_prod_type _).symm
      _ = ∑ u : classVertices classes i, log (rho u) := (e i).sum_comp (fun u : classVertices classes i => log (rho u))
      _ = _ := Finset.sum_coe_sort (classVertices classes i) (fun u => log (rho u))
  change (∑ a, ∑ x, log (rho (e i (a,x)))) ≤ _
  rw [heq]
  have hh := rho_geomean_log_bound G classes i hsizes ell L ht ht1
  have hc : (0 : ℝ) < (classVertices classes i).card := by
    exact_mod_cast (by have := hsizes i; omega : 0 < (classVertices classes i).card)
  have hh' := (div_le_iff₀ hc).mp hh
  rw [hcard, Nat.cast_mul] at hh'
  exact hh'.trans_eq (by ring)

/-- Equation block-max-product-all for the graph's sorted nonneighbor
blocks. The selected eligible blocks can be chosen after seeing a part. -/
theorem sorted_nonneighbor_max_product {n k s L : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (ell : Fin k → ℕ)
    (hL : 0 < L) (hsum : ∑ i, ell i = L) (hs : 0 < s)
    (e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i)
    (theta : ∀ i, Fin (ell i) → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (htheta : ∀ i a, t ≤ theta i a)
    (hshift : ∀ i a (ha : a.val+1 < ell i) x,
      theta i a ≤ nonneighborWeight G classes ell L t (e i (⟨a.val+1,ha⟩,x)))
    (hmean : ∀ i, (∑ a, ∑ x, log (nonneighborWeight G classes ell L t (e i (a,x)))) ≤
      (s : ℝ)*(ell i)*(∑ j, ((ell j : ℝ)/L)*log (min 1 (1-blockDensity G classes i j+t))))
    (M : ∀ i, Finset (Fin (ell i)))
    (heligible : ∀ i a, a ∈ M i → a.val+1 < ell i) :
    (∏ i, ∏ a ∈ M i, (theta i a)^L) ≤
      (∏ i, ∏ j, (min 1 (1-blockDensity G classes i j+t))^(ell i*ell j)) *
        t^(-((L : ℝ)*((L : ℝ)-∑ i, ((M i).card : ℝ)))) := by
  exact block_max_product_all ell hL hsum hs
    (fun i a x => nonneighborWeight G classes ell L t (e i (a,x))) theta M
    (fun i j => min 1 (1-blockDensity G classes i j+t)) ht
    (fun i j => lt_min (by norm_num) (by linarith [blockDensity_le_one G classes i j]))
    (fun i a x => (rho_bounds G classes ell L hL hsum ht ht1 _).1)
    (fun i a _ => ht.trans_le (htheta i a)) heligible
    (fun i a ha x => hshift i a (heligible i a ha) x) hmean

end HadwigerRamsey.ThomasonUpper
