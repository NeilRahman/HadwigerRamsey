import HadwigerRamsey.ThomasonUpper.Regularization

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- The exact quantity P in A.1, retained as a function for the uniform
asymptotic estimates of A.3. The input q is the complementary density. -/
noncomputable def partitionFailure {k : ℕ} (ell : Fin k → ℕ)
    (q : Fin k → Fin k → ℝ) (tau omega phi : ℝ) : ℝ :=
  (2*omega)^(∑ i, ell i) *
    tau^(-((∑ i, (ell i : ℝ))*(k+phi*(∑ i, (ell i : ℝ))))) *
      ∏ i, ∏ j, (min 1 (q i j+tau))^(ell i*ell j)

theorem partitionFailure_pos {k : ℕ} (ell : Fin k → ℕ)
    (q : Fin k → Fin k → ℝ) {tau omega phi : ℝ}
    (htau : 0 < tau) (homega : 0 < omega) (hq : ∀ i j, 0 ≤ q i j) :
    0 < partitionFailure ell q tau omega phi := by
  unfold partitionFailure
  apply mul_pos
  · exact mul_pos (pow_pos (by linarith) _) (rpow_pos_of_pos htau _)
  · exact prod_pos (fun i _ => prod_pos (fun j _ =>
      pow_pos (lt_min (by norm_num) (by linarith [hq i j])) _))

/-- Taking logarithms of P yields the negative quadratic regularized
entropy term, with the exact rounded proportions ell_i/ell. -/
theorem log_partitionFailure {k L : ℕ} (ell : Fin k → ℕ)
    (q : Fin k → Fin k → ℝ) (hL : 0 < L) (hsum : ∑ i, ell i = L)
    {tau omega phi : ℝ} (htau : 0 < tau) (homega : 0 < omega)
    (hq : ∀ i j, 0 ≤ q i j) :
    log (partitionFailure ell q tau omega phi) =
      (L : ℝ)*log (2*omega) - (L : ℝ)*(k+phi*L)*log tau -
        (L : ℝ)^2*regularizedLambda (fun i => (ell i : ℝ)/L) q tau := by
  let d := fun i j => min 1 (q i j+tau)
  have hd : ∀ i j, 0 < d i j := fun i j =>
    lt_min (by norm_num) (by linarith [hq i j])
  have hprod : 0 < ∏ i, ∏ j, (d i j)^(ell i*ell j) :=
    prod_pos (fun i _ => prod_pos (fun j _ => pow_pos (hd i j) _))
  have hsR : ∑ i, (ell i : ℝ) = L := by exact_mod_cast hsum
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hentropy : -(L : ℝ)^2*regularizedLambda (fun i => (ell i : ℝ)/L) q tau =
      ∑ i, ∑ j, ((ell i*ell j : ℕ) : ℝ)*log (d i j) := by
    unfold regularizedLambda regularizedLog
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    dsimp only [d]
    push_cast
    field_simp
    <;> ring
  unfold partitionFailure
  rw [hsum,hsR,log_mul (mul_pos (pow_pos (by linarith) _) (rpow_pos_of_pos htau _)).ne' hprod.ne',
    log_mul (pow_pos (by linarith) _).ne' (rpow_pos_of_pos htau _).ne',log_pow,log_rpow htau]
  have hlogprod : log (∏ i, ∏ j, (d i j)^(ell i*ell j)) =
      ∑ i, ∑ j, ((ell i*ell j : ℕ) : ℝ)*log (d i j) := by
    rw [log_prod (fun i _ => (prod_pos (fun j _ => pow_pos (hd i j) _)).ne')]
    apply sum_congr rfl
    intro i hi
    rw [log_prod (fun j _ => (pow_pos (hd i j) _).ne')]
    simp only [log_pow]
  change _ + log (∏ i, ∏ j, (d i j)^(ell i*ell j)) = _
  rw [hlogprod,← hentropy]
  ring

end HadwigerRamsey.ThomasonUpper
