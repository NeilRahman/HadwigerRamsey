import Mathlib

open scoped BigOperators
open Finset

namespace HadwigerRamsey.FOpt

/-- A cubic envelope whose finite-sum inequality follows from superadditivity. -/
noncomputable def cubic (F a x : ℝ) : ℝ := F*x + a*x*(x-1/2)*(1-x)

lemma cubic_add {F a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x+y ≤ 1) : cubic F a x + cubic F a y ≤ cubic F a (x+y) := by
  have h := mul_nonneg (mul_nonneg (mul_nonneg ha hx) hy) (sub_nonneg.mpr hxy)
  dsimp [cubic]
  nlinarith only [h]

lemma sum_cubic_le {ι : Type*} (s : Finset ι) (α : ι → ℝ) {F a : ℝ}
    (ha : 0 ≤ a) (hα : ∀ i ∈ s, 0 ≤ α i) (hs : ∑ i ∈ s, α i ≤ 1) :
    ∑ i ∈ s, cubic F a (α i) ≤ cubic F a (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubic]
  | @insert i s hi ih =>
    have hnonneg : 0 ≤ ∑ j ∈ s, α j := sum_nonneg (fun j hj => hα j (mem_insert_of_mem hj))
    have hsum : ∑ j ∈ s, α j ≤ 1 := by
      rw [sum_insert hi] at hs
      linarith [hα i (mem_insert_self _ _)]
    rw [sum_insert hi, sum_insert hi]
    exact (add_le_add_left (ih (fun j hj => hα j (mem_insert_of_mem hj)) hsum) _).trans
      (cubic_add ha (hα i (mem_insert_self _ _)) hnonneg (by simpa [sum_insert hi] using hs))

/-- Any function below this cubic has the required partition-of-one inequality. -/
theorem sum_le_of_cubic_envelope {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (f : ℝ → ℝ) {F a : ℝ} (ha : 0 ≤ a)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ cubic F a x)
    (hα : ∀ i ∈ s, 0 ≤ α i) (hs : ∑ i ∈ s, α i = 1) :
    ∑ i ∈ s, f (α i) ≤ F := by
  have hα1 : ∀ i ∈ s, α i ≤ 1 := by
    intro i hi
    rw [← hs]
    exact single_le_sum hα hi
  calc
    _ ≤ ∑ i ∈ s, cubic F a (α i) := sum_le_sum (fun i hi => hf _ ⟨hα i hi,hα1 i hi⟩)
    _ ≤ cubic F a (∑ i ∈ s, α i) := sum_cubic_le s α ha hα hs.le
    _ = F := by simp [hs,cubic]

end HadwigerRamsey.FOpt
