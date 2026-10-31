import HadwigerRamsey.Opt

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey.Optimization

/-- Reindex the manuscript theorem by an arbitrary finite type. -/
lemma opt_fintype {ι : Type*} [Fintype ι] (α p : ι → ℝ) (qB qG : ι → ι → ℝ)
    (hα : ∀ i, 0 < α i) (hs : ∑ i, α i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hB0 : ∀ i j, 0 ≤ qB i j) (hB1 : ∀ i j, qB i j < 1)
    (hG0 : ∀ i j, 0 ≤ qG i j) (hG1 : ∀ i j, qG i j < 1)
    (hd : ∀ i, p i + qB i i + qG i i = 1)
    (ho : ∀ i j, i ≠ j → qB i j + qG i j = 1) :
    (∃ i, beta ≤ α i * sqrt (logCost (p i))) ∨
      beta ≤ sqrt (∑ i, ∑ j, α i*α j*logCost (qB i j)) ∨
      beta ≤ sqrt (∑ i, ∑ j, α i*α j*logCost (qG i j)) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hs' : ∑ i, α (e i) = 1 := by rw [e.sum_comp]; exact hs
  have h := HadwigerRamsey.opt (Fintype.card ι) (fun i => α (e i)) (fun i => p (e i))
    (fun i j => qB (e i) (e j)) (fun i j => qG (e i) (e j))
    (fun i => hα _) hs' (fun i => hp0 _) (fun i => hp1 _)
    (fun i j => hB0 _ _) (fun i j => hB1 _ _) (fun i j => hG0 _ _) (fun i j => hG1 _ _)
    (fun i => hd _) (fun i j hij => ho _ _ (fun he => hij (e.injective he)))
  have he (q : ι → ι → ℝ) :
      -(∑ i, ∑ j, α (e i)*α (e j)*log (1-q (e i) (e j))) =
        ∑ i, ∑ j, α i*α j*logCost (q i j) := by
    simp only [logCost,mul_neg,← sum_neg_distrib]
    refine Fintype.sum_equiv e _ _ ?_
    intro i
    exact Fintype.sum_equiv e _ _ (fun j => rfl)
  rcases h with h | h | h
  · exact Or.inl ⟨e h.choose,h.choose_spec⟩
  · exact Or.inr (Or.inl (by rwa [he] at h))
  · exact Or.inr (Or.inr (by rwa [he] at h))

/-- Removing zero weights preserves every weighted sum. -/
lemma sum_positive_support {k : ℕ} (α : Fin k → ℝ) (hα : ∀ i, 0 ≤ α i)
    (f : Fin k → ℝ) :
    (∑ i, α i*f i) = ∑ i : {i // 0 < α i}, α i.val*f i.val := by
  classical
  refine Finset.sum_congr_set {i | 0 < α i} _ _ (fun _ _ => rfl) ?_
  intro i hi
  have hz : α i = 0 := by
    simp only [Set.mem_setOf_eq] at hi
    linarith [hα i]
  simp [hz]


/-- The zero-weight extension is derived by restricting to the positive support and applying opt. -/
lemma opt_nonneg_equalities_from_opt (k : ℕ) (α p : Fin k → ℝ) (qB qG : Fin k → Fin k → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hB0 : ∀ i j, 0 ≤ qB i j) (hB1 : ∀ i j, qB i j < 1)
    (hG0 : ∀ i j, 0 ≤ qG i j) (hG1 : ∀ i j, qG i j < 1)
    (hd : ∀ i, p i + qB i i + qG i i = 1)
    (ho : ∀ i j, i ≠ j → qB i j + qG i j = 1) :
    (∃ i, beta ≤ α i * sqrt (logCost (p i))) ∨
      beta ≤ sqrt (energy α qB) ∨ beta ≤ sqrt (energy α qG) := by
  classical
  let S := {i : Fin k // 0 < α i}
  have hs' : ∑ i : S, α i.val = 1 := by
    have hh := sum_positive_support α hα (fun _ => 1)
    simpa only [mul_one,hs] using hh.symm
  have he (q : Fin k → Fin k → ℝ) : energy α q =
      ∑ i : S, ∑ j : S, α i.val*α j.val*logCost (q i.val j.val) := by
    dsimp [energy]
    simp_rw [mul_assoc,← mul_sum]
    rw [sum_positive_support α hα]
    apply sum_congr rfl
    intro i hi
    congr 1
    rw [sum_positive_support α hα]
  have hh := opt_fintype (fun i : S => α i.val) (fun i : S => p i.val)
    (fun i j : S => qB i.val j.val) (fun i j : S => qG i.val j.val)
    (fun i => i.property) hs' (fun i => hp0 _) (fun i => hp1 _)
    (fun i j => hB0 _ _) (fun i j => hB1 _ _) (fun i j => hG0 _ _) (fun i j => hG1 _ _)
    (fun i => hd _) (fun i j hij => ho _ _ (fun hv => hij (Subtype.ext hv)))
  rcases hh with h | h | h
  · exact Or.inl ⟨h.choose.val,h.choose_spec⟩
  · exact Or.inr (Or.inl (by rwa [← he] at h))
  · exact Or.inr (Or.inr (by rwa [← he] at h))

lemma energy_mono {k : ℕ} {α : Fin k → ℝ} {q q' : Fin k → Fin k → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hle : ∀ i j, q i j ≤ q' i j) (hq' : ∀ i j, q' i j < 1) :
    energy α q ≤ energy α q' :=
  sum_le_sum (fun i _ => sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
    (logCost_mono (hle i j) (hq' i j)) (mul_nonneg (hα i) (hα j))))

/-- Rescale each triple or pair down to total mass one, then use the zero-weight extension of opt. -/
theorem opt_closed_from_opt (k : ℕ) (α p : Fin k → ℝ) (qB qG : Fin k → Fin k → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hs : ∑ i, α i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hB0 : ∀ i j, 0 ≤ qB i j) (hB1 : ∀ i j, qB i j < 1)
    (hG0 : ∀ i j, 0 ≤ qG i j) (hG1 : ∀ i j, qG i j < 1)
    (hd : ∀ i, 1 ≤ p i + qB i i + qG i i)
    (ho : ∀ i j, i ≠ j → 1 ≤ qB i j + qG i j) :
    (∃ i, beta ≤ α i * sqrt (logCost (p i))) ∨
      beta ≤ sqrt (energy α qB) ∨ beta ≤ sqrt (energy α qG) := by
  classical
  let d (i j : Fin k) := if i = j then p i+qB i i+qG i i else qB i j+qG i j
  have hd1 (i j) : 1 ≤ d i j := by dsimp [d]; split_ifs with h; exact hd i; exact ho i j h
  have hdp (i j) : 0 < d i j := lt_of_lt_of_le zero_lt_one (hd1 i j)
  let p' i := p i / d i i
  let b' i j := qB i j / d i j
  let g' i j := qG i j / d i j
  have hple i : p' i ≤ p i := div_le_self (hp0 i) (hd1 i i)
  have hble i j : b' i j ≤ qB i j := div_le_self (hB0 i j) (hd1 i j)
  have hgle i j : g' i j ≤ qG i j := div_le_self (hG0 i j) (hd1 i j)
  have heqd i : p' i + b' i i + g' i i = 1 := by
    dsimp [p',b',g']
    rw [← add_div,← add_div,div_eq_one_iff_eq (hdp i i).ne']
    simp [d]
  have heqo i j (hij : i ≠ j) : b' i j + g' i j = 1 := by
    dsimp [b',g']
    rw [← add_div,div_eq_one_iff_eq (hdp i j).ne']
    simp [d,hij]
  have hh := opt_nonneg_equalities_from_opt k α p' b' g' hα hs
    (fun i => div_nonneg (hp0 i) (hdp i i).le) (fun i => (hple i).trans_lt (hp1 i))
    (fun i j => div_nonneg (hB0 i j) (hdp i j).le) (fun i j => (hble i j).trans_lt (hB1 i j))
    (fun i j => div_nonneg (hG0 i j) (hdp i j).le) (fun i j => (hgle i j).trans_lt (hG1 i j)) heqd heqo
  rcases hh with h | h | h
  · obtain ⟨i,hi⟩ := h
    exact Or.inl ⟨i,hi.trans (mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt (logCost_mono (hple i) (hp1 i))) (hα i))⟩
  · exact Or.inr (Or.inl (h.trans (sqrt_le_sqrt (energy_mono hα hble hB1))))
  · exact Or.inr (Or.inr (h.trans (sqrt_le_sqrt (energy_mono hα hgle hG1))))

end HadwigerRamsey.Optimization
