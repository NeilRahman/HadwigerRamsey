import HadwigerRamsey.ThomasonUpper.Density
import HadwigerRamsey.ThomasonUpper.Rounding

open scoped BigOperators
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- The finite trimming step in A.3: rounded class counts can be made
exact multiples of one common integer, deleting at most n/(aℓ)+ℓ vertices.
The bound is uniform in the partition and its number of classes. -/
theorem exact_multiple_trimming {n k ℓ : ℕ} (τ : Fin n → Fin k)
    (hn : 0 < n) (hℓ : 0 < ℓ) {a : ℝ} (ha : 0 < a)
    (hα : ∀ i, a ≤ classMass τ i)
    (m : Fin k → ℕ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = ℓ)
    (herr : ∀ i, |(m i : ℝ) - classMass τ i * ℓ| ≤ 1) :
    ∃ s : ℕ, ∃ X : Fin k → Finset (Fin n),
      (∀ i, X i ⊆ classVertices τ i ∧ (X i).card = s*m i) ∧
      (univ.biUnion X).card = s*ℓ ∧
      (n : ℝ) - s*ℓ ≤ (n : ℝ)/(a*ℓ) + ℓ := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hk : Nonempty (Fin k) := ⟨τ ⟨0, hn⟩⟩
  let q := fun i => ⌊((classVertices τ i).card : ℝ) / (m i : ℝ)⌋₊
  obtain ⟨j, _, hj⟩ := exists_min_image (univ : Finset (Fin k)) q univ_nonempty
  let s := q j
  have hsbound : ∀ i, s*m i ≤ (classVertices τ i).card := by
    intro i
    have hs : (s : ℝ) ≤ ((classVertices τ i).card : ℝ) / m i := by
      calc
        _ ≤ (q i : ℝ) := by exact_mod_cast hj i (mem_univ _)
        _ ≤ _ := Nat.floor_le (by positivity)
    have hmi : (0 : ℝ) < m i := by exact_mod_cast hm i
    exact_mod_cast (le_div_iff₀ hmi).mp hs
  choose X hX hcard using fun i => exists_subset_card_eq (hsbound i)
  have hdisj : ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint X := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hi := (mem_filter.mp (hX i hxi)).2
    have hj := (mem_filter.mp (hX j hxj)).2
    exact hij (hi.symm.trans hj)
  refine ⟨s, X, fun i => ⟨hX i, hcard i⟩, ?_, ?_⟩
  · rw [card_biUnion hdisj]
    simp_rw [hcard]
    rw [← mul_sum, hsum]
  · have hmj : (0 : ℝ) < m j := by exact_mod_cast hm j
    have hαj : 0 < classMass τ j := ha.trans_le (hα j)
    have hαN : classMass τ j * n = ((classVertices τ j).card : ℝ) := by
      change (((classVertices τ j).card : ℝ) / n) * n = _
      exact div_mul_cancel₀ _ hnR.ne'
    have hup : (m j : ℝ) ≤ classMass τ j * ℓ + 1 := by
      have hh := (abs_le.mp (herr j)).2
      linarith
    have hratio : (1 : ℝ) ≤ classMass τ j / a :=
      (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hα j)
    have hden : 0 < (ℓ : ℝ) + 1/a := by positivity
    have hquot : (n : ℝ)/((ℓ : ℝ)+1/a) ≤
        ((classVertices τ j).card : ℝ)/(m j : ℝ) := by
      apply (div_le_div_iff₀ hden hmj).mpr
      have hh : (m j : ℝ) ≤ classMass τ j * ((ℓ : ℝ)+1/a) := by
        calc
          _ ≤ classMass τ j * ℓ + 1 := hup
          _ ≤ classMass τ j * ℓ + classMass τ j/a := by linarith
          _ = _ := by ring
      have hhN := mul_le_mul_of_nonneg_left hh hnR.le
      nlinarith [hαN]
    have hfloor := Nat.lt_floor_add_one (((classVertices τ j).card : ℝ)/(m j : ℝ))
    change ((classVertices τ j).card : ℝ)/(m j : ℝ) < (s : ℝ)+1 at hfloor
    have hslo : (n : ℝ) ≤ ((s : ℝ)+1)*((ℓ : ℝ)+1/a) :=
      ((div_le_iff₀ hden).mp (hquot.trans hfloor.le))
    have hloss : (n : ℝ) - s*ℓ ≤ (n : ℝ)/(a*ℓ+1) + ℓ := by
      have hden2 : 0 < a*(ℓ : ℝ)+1 := by positivity
      have hsloA := mul_le_mul_of_nonneg_right hslo ha.le
      have hc : ((s : ℝ)+1)*((ℓ : ℝ)+1/a)*a = ((s : ℝ)+1)*(a*ℓ+1) := by
        field_simp
      rw [hc] at hsloA
      have hh := mul_le_mul_of_nonneg_right hsloA hℓR.le
      have htarget : ((n : ℝ) - s*ℓ - ℓ) * (a*ℓ+1) ≤ n := by
        nlinarith
      exact (sub_le_iff_le_add).mp ((le_div_iff₀ hden2).mpr htarget)
    have hfrac : (n : ℝ)/(a*ℓ+1) ≤ (n : ℝ)/(a*ℓ) :=
      div_le_div_of_nonneg_left hnR.le (mul_pos ha hℓR) (by linarith)
    linarith

/-- Rounding and trimming together, with positive common multiplicity and
an explicit deleted fraction. The two largeness hypotheses hold in the
manuscript's eventual square-root-logarithmic regime. -/
theorem rounded_class_trimming {n k ℓ : ℕ} (τ : Fin n → Fin k)
    (hn : 0 < n) (hℓ : 0 < ℓ) {a : ℝ} (ha : 0 < a)
    (hα : ∀ i, a ≤ classMass τ i) (hlarge : 2 ≤ a*ℓ) (hscale : 4*ℓ ≤ n) :
    ∃ m : Fin k → ℕ, ∃ s : ℕ, ∃ X : Fin k → Finset (Fin n),
      (∀ i, 0 < m i) ∧ (∑ i, m i) = ℓ ∧ 0 < s ∧
      (∀ i, |(m i : ℝ)/(ℓ : ℝ)-classMass τ i| ≤ 1/(ℓ : ℝ)) ∧
      (∀ i, X i ⊆ classVertices τ i ∧ (X i).card = s*m i) ∧
      (univ.biUnion X).card = s*ℓ ∧
      ((n : ℝ)-(univ.biUnion X).card)/(n : ℝ) ≤ 1/(a*ℓ)+(ℓ : ℝ)/n := by
  classical
  obtain ⟨m, hsum, herr, hfloor⟩ := rounded_counts (classMass τ)
    (classMass_nonneg τ) (sum_classMass hn τ) ℓ
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : ∀ i, 0 < m i := by
    intro i
    have hi : 1 ≤ classMass τ i * ℓ := by
      have hh := mul_le_mul_of_nonneg_right (hα i) hℓR.le
      linarith
    exact (Nat.floor_pos.mpr hi).trans_le (hfloor i)
  obtain ⟨s, X, hX, hcard, hloss⟩ := exact_multiple_trimming τ hn hℓ ha hα m hm hsum herr
  have hs : 0 < s := by
    by_contra h
    have hs0 : s = 0 := by omega
    have hhalf : (n : ℝ)/(a*ℓ) ≤ (n : ℝ)/2 := by
      exact div_le_div_of_nonneg_left hnR.le (by norm_num : (0:ℝ) < 2) hlarge
    have hscaleR : (4 : ℝ)*ℓ ≤ n := by exact_mod_cast hscale
    simp only [hs0, Nat.cast_zero, zero_mul, sub_zero] at hloss
    linarith
  refine ⟨m, s, X, hm, hsum, hs, ?_, hX, hcard, ?_⟩
  · intro i
    have he : (m i : ℝ)/(ℓ : ℝ)-classMass τ i =
        ((m i : ℝ)-classMass τ i*ℓ)/(ℓ : ℝ) := by field_simp
    rw [he, abs_div, abs_of_pos hℓR]
    exact div_le_div_of_nonneg_right (herr i) hℓR.le
  · rw [hcard, Nat.cast_mul]
    apply (div_le_iff₀ hnR).mpr
    have he : (1/(a*(ℓ : ℝ))+(ℓ : ℝ)/n)*(n : ℝ) = (n : ℝ)/(a*ℓ)+ℓ := by field_simp
    rw [he]
    exact hloss

end HadwigerRamsey.ThomasonUpper
