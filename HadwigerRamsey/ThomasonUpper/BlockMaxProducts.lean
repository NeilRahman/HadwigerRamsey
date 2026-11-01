import HadwigerRamsey.ThomasonUpper.SortedBlocks

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- The multitype product of selected sorted-block maxima, with precisely
the exponent and ordered double product in equation block-max-product-all. -/
theorem block_max_product_all {k s L : ℕ} (ell : Fin k → ℕ)
    (hL : 0 < L) (hsum : ∑ i, ell i = L) (hs : 0 < s)
    (rho : ∀ i, Fin (ell i) → Fin s → ℝ)
    (theta : ∀ i, Fin (ell i) → ℝ) (M : ∀ i, Finset (Fin (ell i)))
    (q : Fin k → Fin k → ℝ) {t : ℝ} (ht : 0 < t)
    (hq : ∀ i j, 0 < q i j)
    (hrho : ∀ i a x, t ≤ rho i a x)
    (htheta : ∀ i a, a ∈ M i → 0 < theta i a)
    (heligible : ∀ i a, a ∈ M i → a.val+1 < ell i)
    (hshift : ∀ i a, ∀ ha : a ∈ M i, ∀ x : Fin s,
      theta i a ≤ rho i ⟨a.val+1, heligible i a ha⟩ x)
    (hmean : ∀ i, (∑ a, ∑ x, log (rho i a x)) ≤
      (s : ℝ)*(ell i)*(∑ j, ((ell j : ℝ)/L)*log (q i j))) :
    (∏ i, ∏ a ∈ M i, (theta i a)^L) ≤
      (∏ i, ∏ j, (q i j)^(ell i*ell j)) *
        t^(-((L : ℝ)*((L : ℝ)-∑ i, ((M i).card : ℝ)))) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hi : ∀ i, (∑ a ∈ M i, log (theta i a)) ≤
      (ell i : ℝ)*(∑ j, ((ell j : ℝ)/L)*log (q i j)) -
        ((ell i : ℝ)-(M i).card)*log t := by
    intro i
    have hh := sorted_block_log_bound hs (rho i) (theta i) (M i) ht
      (hrho i) (htheta i) (heligible i) (hshift i)
    have hm := hmean i
    nlinarith
  have htotal := sum_le_sum (s := univ) (fun i _ => hi i)
  have hell : ∑ i, (ell i : ℝ) = L := by exact_mod_cast hsum
  simp only [sum_sub_distrib] at htotal
  have hmissing : (∑ i, ((ell i : ℝ)-(M i).card)*log t) =
      ((L : ℝ)-∑ i, ((M i).card : ℝ))*log t := by
    rw [← sum_mul, sum_sub_distrib, hell]
  rw [hmissing] at htotal
  have hLnonneg : (0 : ℝ) ≤ L := by positivity
  have hexpand : (L : ℝ)*(∑ i, (ell i : ℝ)*(∑ j, ((ell j : ℝ)/L)*log (q i j))) =
      ∑ i, ∑ j, ((ell i*ell j : ℕ) : ℝ)*log (q i j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro j hj
    push_cast
    field_simp
  have hbound : (L : ℝ)*(∑ i, ∑ a ∈ M i, log (theta i a)) ≤
      (∑ i, ∑ j, ((ell i*ell j : ℕ) : ℝ)*log (q i j)) -
        (L : ℝ)*((L : ℝ)-∑ i, ((M i).card : ℝ))*log t := by
    rw [← hexpand]
    nlinarith
  have hp : 0 < ∏ i, ∏ a ∈ M i, (theta i a)^L :=
    prod_pos (fun i _ => prod_pos (fun a ha => pow_pos (htheta i a ha) _))
  have hqp : 0 < ∏ i, ∏ j, (q i j)^(ell i*ell j) :=
    prod_pos (fun i _ => prod_pos (fun j _ => pow_pos (hq i j) _))
  apply (log_le_log_iff hp (mul_pos hqp (rpow_pos_of_pos ht _))).mp
  rw [log_mul hqp.ne' (rpow_pos_of_pos ht _).ne', log_rpow ht]
  rw [log_prod (fun i _ => (prod_pos (fun a ha => pow_pos (htheta i a ha) L)).ne')]
  rw [log_prod (fun i _ => (prod_pos (fun j _ => pow_pos (hq i j) (ell i*ell j))).ne')]
  simp_rw [log_prod (fun a ha => (pow_pos (htheta _ a ha) L).ne'), log_pow]
  simp_rw [log_prod (fun j _ => (pow_pos (hq _ j) _).ne'), log_pow]
  simp_rw [← mul_sum]
  nlinarith

end HadwigerRamsey.ThomasonUpper
