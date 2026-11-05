/-
The finite-tuple energy iteration adapts Graphon.Regularity.regularity,
Copyright (c) 2026 Cameron Freer. Released under the Apache 2.0 license;
see vendor/graphon/LICENSE and vendor/graphon/README.md.
-/
import Graphon.Regularity

open scoped BigOperators Classical
open MeasureTheory Finset

namespace ComponentTransfer.Transfer

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- Uniform cell bound for a common weak regularity partition of `r` kernels. -/
noncomputable def commonRegularityBound (r : ℕ) (ε : ℝ) : ℕ :=
  4 ^ (Nat.ceil ((r : ℝ)/ε^2)+1)

/-- Weak regularity for a finite tuple, with a single partition. The energy
increment refines for one offending colour and preserves every other colour's
energy, so the sum of the energies bounds the number of refinements. -/
theorem common_regularity {r : ℕ} (W : Fin r → Graphon α μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : MeasurablePartition α μ,
      P.parts.card ≤ commonRegularityBound r ε ∧
      ∀ c, Graphon.cutNormDiff (W c) (Graphon.stepify P (W c)) ≤ ε := by
  let N : ℕ := Nat.ceil ((r : ℝ)/ε^2)+1
  let E : MeasurablePartition α μ → ℝ := fun P => ∑ c, Graphon.energy (W c) P
  have hE0 (P) : 0 ≤ E P := sum_nonneg (fun c _ => Graphon.energy_nonneg (W c) P)
  have hE1 (P) : E P ≤ r := by
    have h := sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin r))) => Graphon.energy_le_one (W c) P)
    simpa [E] using h
  have increment (P : MeasurablePartition α μ)
      (hbad : ¬ ∀ c, Graphon.cutNormDiff (W c) (Graphon.stepify P (W c)) ≤ ε) :
      ∃ Q : MeasurablePartition α μ, Q.parts.card ≤ 4*P.parts.card ∧ E P+ε^2 ≤ E Q := by
    push Not at hbad
    obtain ⟨c,hc⟩ := hbad
    obtain ⟨Q,_,hcard,hgain,hmono⟩ := Graphon.energy_increment_pair (W c) P ε hε hc
    refine ⟨Q,hcard,?_⟩
    have hrest : ∑ d ∈ univ.erase c, Graphon.energy (W d) P ≤
        ∑ d ∈ univ.erase c, Graphon.energy (W d) Q :=
      sum_le_sum (fun d _ => hmono (W d))
    have hp := sum_erase_add (univ : Finset (Fin r)) (fun d => Graphon.energy (W d) P) (mem_univ c)
    have hq := sum_erase_add (univ : Finset (Fin r)) (fun d => Graphon.energy (W d) Q) (mem_univ c)
    dsimp only [E]
    linarith
  have iterate : ∀ n : ℕ, n ≤ N → ∀ P : MeasurablePartition α μ,
      P.parts.card ≤ 4^(N-n) → ∃ Q : MeasurablePartition α μ,
        Q.parts.card ≤ 4^N ∧
          ((∀ c, Graphon.cutNormDiff (W c) (Graphon.stepify Q (W c)) ≤ ε) ∨
            E P+(n : ℝ)*ε^2 ≤ E Q) := by
    intro n
    induction n with
    | zero =>
      intro hn P hcard
      exact ⟨P,by simpa using hcard,Or.inr (by simp)⟩
    | succ n ih =>
      intro hn P hcard
      by_cases hgood : ∀ c, Graphon.cutNormDiff (W c) (Graphon.stepify P (W c)) ≤ ε
      · exact ⟨P,hcard.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le N _)),Or.inl hgood⟩
      obtain ⟨Q,hQcard,hgain⟩ := increment P hgood
      have hcard' : Q.parts.card ≤ 4^(N-n) := by
        have heq : N-n = (N-(n+1))+1 := by omega
        calc Q.parts.card ≤ 4*P.parts.card := hQcard
          _ ≤ 4*4^(N-(n+1)) := Nat.mul_le_mul_left _ hcard
          _ = 4^(N-n) := by rw [heq,pow_succ]; ring
      obtain ⟨R,hR,hresult⟩ := ih (by omega) Q hcard'
      refine ⟨R,hR,?_⟩
      rcases hresult with hg | he
      · exact Or.inl hg
      · right
        push_cast
        linarith
  obtain ⟨P,hcard,hresult⟩ := iterate N le_rfl (Graphon.trivialPartition (α := α) (μ := μ))
    (by simp [Graphon.trivialPartition_card])
  rcases hresult with hg | he
  · exact ⟨P,hcard,hg⟩
  · have hlarge : (r : ℝ) < (N : ℝ)*ε^2 := by
      have hceil := Nat.le_ceil ((r : ℝ)/ε^2)
      have hpow : 0 < ε^2 := sq_pos_of_pos hε
      have hmult := (div_le_iff₀ hpow).mp hceil
      dsimp [N]
      push_cast
      nlinarith
    have := hE0 (Graphon.trivialPartition (α := α) (μ := μ))
    have := hE1 P
    linarith

end ComponentTransfer.Transfer
