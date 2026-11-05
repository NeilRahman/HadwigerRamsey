import HadwigerRamsey4Col.Lemma4
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

noncomputable def pairWeight (a : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  weight+(a i+a j-1/2)/2
noncomputable def rowWeight (a : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j ∈ univ.erase i, pairWeight a i j
noncomputable def diagonalDual (a : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j ∈ univ.erase i, pairWeight a i j*log (rowWeight a i/(2*pairWeight a i j))
/-- The manuscript's `N(a)`. The off-diagonal term is an ordered sum,
which equals twice the sum over `i < j`. -/
noncomputable def dualValue (a : Fin 4 → ℝ) : ℝ :=
  ∑ i, a i^2*diagonalDual a i +
    ∑ i, ∑ j ∈ univ.erase i, a i*a j*entropy (pairWeight a i j)
noncomputable def moment (a : Fin 4 → ℝ) (n : ℕ) : ℝ := ∑ i, a i^n
noncomputable def centeredMoment (a : Fin 4 → ℝ) (n : ℕ) : ℝ :=
  ∑ i, (a i-1/4)^n
noncomputable def uniformValue : ℝ := (3/4 : ℝ)*(weight*log (3/2)+entropy weight)

theorem pairWeight_symm (a : Fin 4 → ℝ) (i j : Fin 4) :
    pairWeight a i j = pairWeight a j i := by unfold pairWeight; ring

lemma rowWeight_eq {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1) (i : Fin 4) :
    rowWeight a i = shiftedWeight+a i := by
  have hs' : a 3 = 1-a 0-a 1-a 2 := by
    simp [Fin.sum_univ_succ] at hs
    linarith
  fin_cases i <;> simp [rowWeight, pairWeight, shiftedWeight,
    sum_erase_eq_sub, Fin.sum_univ_succ, hs'] <;> ring

lemma pair_mass_bounds {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (i j : Fin 4) (hij : i ≠ j) :
    (1/5 : ℝ) ≤ a i+a j ∧ a i+a j ≤ 4/5 := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have h3 := hu 3
  simp [Fin.sum_univ_succ] at hs
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num <;> constructor <;> linarith!

lemma pairWeight_pos {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i) (i j : Fin 4) :
    0 < pairWeight a i j := by
  dsimp [pairWeight]
  linarith [weight_bounds.1, hn i, hn j]

lemma pairWeight_shift_bound {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (i j : Fin 4) (hij : i ≠ j) :
    |(a i+a j-1/2)/2| ≤ (3/20 : ℝ) := by
  obtain ⟨hl,hu⟩ := pair_mass_bounds hs hu i j hij
  rw [abs_le]
  constructor <;> linarith

lemma rowWeight_bounds {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1)
    (hn : ∀ i, 0 ≤ a i) (hu : ∀ i, a i ≤ (2/5 : ℝ)) (i : Fin 4) :
    (3/4 : ℝ) < rowWeight a i ∧ rowWeight a i < 2 := by
  rw [rowWeight_eq hs i]
  dsimp [shiftedWeight]
  constructor <;> linarith [weight_bounds.1, weight_bounds.2, hn i, hu i]

lemma row_variance_identity {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1) (i : Fin 4) :
    12*(∑ j ∈ univ.erase i, (pairWeight a i j-rowWeight a i/3)^2) =
      3*moment a 2-4*a i^2+2*a i-1 := by
  have hs' : a 3 = 1-a 0-a 1-a 2 := by
    simp [Fin.sum_univ_succ] at hs
    linarith
  rw [rowWeight_eq hs]
  fin_cases i <;> simp [pairWeight, shiftedWeight, moment,
    sum_erase_eq_sub, Fin.sum_univ_succ, hs'] <;> ring

lemma row_penalty_identity {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1) (i : Fin 4)
    (hrow : rowWeight a i ≠ 0) :
    (∑ j ∈ univ.erase i, pairWeight a i j*(3*pairWeight a i j/rowWeight a i-1)) =
      (3*moment a 2-4*a i^2+2*a i-1)/(4*rowWeight a i) := by
  have hs' : a 3 = 1-a 0-a 1-a 2 := by
    simp [Fin.sum_univ_succ] at hs
    linarith
  apply (eq_div_iff (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hrow)).mpr
  rw [sum_mul]
  have hterm (j : Fin 4) :
      pairWeight a i j*(3*pairWeight a i j/rowWeight a i-1)*(4*rowWeight a i) =
        12*(pairWeight a i j)^2-4*rowWeight a i*pairWeight a i j := by
    field_simp [hrow]
    ring
  simp_rw [hterm]
  rw [rowWeight_eq hs]
  fin_cases i <;> simp [pairWeight, shiftedWeight, moment,
    sum_erase_eq_sub, Fin.sum_univ_succ, hs'] <;> ring

end HadwigerRamsey4Col
