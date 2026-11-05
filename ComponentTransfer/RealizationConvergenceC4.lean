import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The four-cycle bound for finite weighted kernels

Two applications of Cauchy--Schwarz control every weighted rectangle of a
finite real matrix by its four-cycle average. The weights may be fractional,
as is necessary when comparing a finite step graphon with a measurable cut.
-/

namespace ComponentTransfer.Realization

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [Nonempty V]

lemma expect_weighted_sq_le (a f : V → ℝ) (ha : ∀ x, |a x| ≤ 1) :
    (𝔼 x, a x * f x) ^ 2 ≤ 𝔼 x, (f x) ^ 2 := by
  have h₁ := expect_mul_sq_le_sq_mul_sq univ a f
  have h₂ : (𝔼 x, a x ^ 2) ≤ 1 := by
    apply expect_le univ_nonempty
    intro x _
    nlinarith [sq_abs (a x), ha x, abs_nonneg (a x)]
  have h₃ : 0 ≤ 𝔼 x, f x ^ 2 := expect_nonneg fun _ _ => sq_nonneg _
  exact h₁.trans (by nlinarith)

/-- The normalized rectangle with fractional row and column weights. -/
noncomputable def finiteRectangle (K : V → V → ℝ) (a b : V → ℝ) : ℝ :=
  𝔼 x, a x * (𝔼 y, K x y * b y)

/-- The nonnegative four-cycle average, written as a Gram-matrix square. -/
noncomputable def finiteC4 (K : V → V → ℝ) : ℝ :=
  𝔼 y, 𝔼 z, (𝔼 x, K x y * K x z) ^ 2

omit [Nonempty V] in
lemma finiteC4_nonneg (K : V → V → ℝ) : 0 ≤ finiteC4 K := by
  exact expect_nonneg fun _ _ => expect_nonneg fun _ _ => sq_nonneg _

omit [Nonempty V] in
lemma finite_row_square_identity (K : V → V → ℝ) (b : V → ℝ) :
    (𝔼 x, (𝔼 y, K x y * b y) ^ 2) =
      𝔼 y, 𝔼 z, (b y * b z) * (𝔼 x, K x y * K x z) := by
  simp_rw [sq, expect_mul_expect]
  rw [expect_comm]
  congr 1
  funext y
  rw [expect_comm]
  apply expect_congr rfl
  intro z _
  rw [mul_expect]
  apply expect_congr rfl
  intro x _
  ring

/-- Every fractional cut is bounded by the fourth root of the four-cycle
average. This is valid for signed matrices and needs no symmetry assumption. -/
theorem finite_rectangle_pow_four_le_C4 (K : V → V → ℝ) (a b : V → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1) :
    finiteRectangle K a b ^ 4 ≤ finiteC4 K := by
  have h₁ := expect_weighted_sq_le a (fun x => 𝔼 y, K x y * b y) ha
  change finiteRectangle K a b ^ 2 ≤ _ at h₁
  have h₂ := expect_weighted_sq_le
    (fun p : V × V => b p.1 * b p.2)
    (fun p : V × V => 𝔼 x, K x p.1 * K x p.2)
    (fun p => by
      rw [abs_mul]
      nlinarith [hb p.1, hb p.2, abs_nonneg (b p.1), abs_nonneg (b p.2)])
  simp only [← univ_product_univ, expect_product] at h₂
  rw [← finite_row_square_identity] at h₂
  change (𝔼 x, (𝔼 y, K x y * b y) ^ 2) ^ 2 ≤ finiteC4 K at h₂
  have h₃ : 0 ≤ 𝔼 x, (𝔼 y, K x y * b y) ^ 2 :=
    expect_nonneg fun _ _ => sq_nonneg _
  nlinarith [sq_nonneg (finiteRectangle K a b)]

omit [Nonempty V] in
/-- The Gram-square definition is exactly the usual four-edge homomorphism
average, including maps which identify some vertices. -/
theorem finiteC4_eq_four_edge_average (K : V → V → ℝ) :
    finiteC4 K = 𝔼 y, 𝔼 z, 𝔼 x, 𝔼 w,
      K x y * K x z * K w y * K w z := by
  unfold finiteC4
  simp_rw [sq, expect_mul_expect]
  apply expect_congr rfl
  intro y _
  apply expect_congr rfl
  intro z _
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro w _
  ring

/-- Four indexed vertices, arranged as the two sides of a bipartite cycle. -/
def fourVertexEquiv (V : Type*) : (Fin 4 → V) ≃ V × (V × (V × V)) where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨y, z, x, w⟩; rfl

omit [Nonempty V] in
/-- The four-cycle average is a normalized sum over maps of four vertices.
Vertices 0 and 1 form one side, and vertices 2 and 3 the other. -/
theorem finiteC4_eq_fin4_sum (K : V → V → ℝ) :
    finiteC4 K =
      (∑ f : Fin 4 → V, K (f 2) (f 0) * K (f 2) (f 1) *
        K (f 3) (f 0) * K (f 3) (f 1)) / (Fintype.card V : ℝ) ^ 4 := by
  have he := Finset.expect_equiv (fourVertexEquiv V)
    (s := (Finset.univ : Finset (Fin 4 → V))) (t := Finset.univ)
    (f := fun f : Fin 4 → V => K (f 2) (f 0) * K (f 2) (f 1) *
      K (f 3) (f 0) * K (f 3) (f 1))
    (g := fun p : V × (V × (V × V)) =>
      K p.2.2.1 p.1 * K p.2.2.1 p.2.1 * K p.2.2.2 p.1 * K p.2.2.2 p.2.1)
    (by simp) (by intros; rfl)
  simp only [← Finset.univ_product_univ, Finset.expect_product] at he
  rw [Finset.expect_eq_sum_div_card] at he
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at he
  rw [finiteC4_eq_four_edge_average]
  exact he.symm

end ComponentTransfer.Realization
