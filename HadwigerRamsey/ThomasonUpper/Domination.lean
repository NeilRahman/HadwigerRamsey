import Mathlib

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- Double counting incidences in a bipartite relation. -/
theorem sum_card_neighbors_comm {V U : Type*} [DecidableEq V] [DecidableEq U]
    (A : Finset V) (B : Finset U) (R : V → U → Prop) [DecidableRel R] :
    (∑ a ∈ A, (B.filter (R a)).card) =
      ∑ b ∈ B, (A.filter fun a => R a b).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Some vertex covers at least the average guaranteed fraction of the
remaining vertices. The lower degree hypothesis is inherited by subsets of A. -/
theorem exists_covering_vertex {V U : Type*} [DecidableEq V] [DecidableEq U]
    (A : Finset V) (B : Finset U) (hB : B.Nonempty)
    (R : V → U → Prop) [DecidableRel R] (θ : ℝ)
    (hdeg : ∀ a ∈ A, θ * (B.card : ℝ) ≤ (B.filter (R a)).card) :
    ∃ b ∈ B, θ * (A.card : ℝ) ≤ (A.filter fun a => R a b).card := by
  by_contra! h
  have hsum : (∑ b ∈ B, ((A.filter fun a => R a b).card : ℝ)) <
      (B.card : ℝ) * (θ * A.card) := by
    calc
      _ < ∑ _b ∈ B, θ * (A.card : ℝ) := Finset.sum_lt_sum_of_nonempty hB h
      _ = _ := by simp
  have hsum' : (A.card : ℝ) * (θ * B.card) ≤
      ∑ a ∈ A, ((B.filter (R a)).card : ℝ) := by
    simpa using Finset.sum_le_sum hdeg
  have heq := congrArg (fun t : ℕ => (t : ℝ)) (sum_card_neighbors_comm A B R)
  simp only [Nat.cast_sum] at heq
  nlinarith

/-- After t greedy choices at most `(1-θ)^t |A|` vertices remain uncovered.
This finite statement also handles an empty left side. -/
theorem greedy_domination {V U : Type*} [DecidableEq V] [DecidableEq U]
    (A : Finset V) (B : Finset U) (hB : B.Nonempty)
    (R : V → U → Prop) [DecidableRel R] (θ : ℝ) (_hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hdeg : ∀ a ∈ A, θ * (B.card : ℝ) ≤ (B.filter (R a)).card) (t : ℕ) :
    ∃ M : Finset U, M ⊆ B ∧ M.card ≤ t ∧
      ((A.filter fun a => ∀ b ∈ M, ¬R a b).card : ℝ) ≤
        (1-θ)^t * A.card := by
  induction t with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨M, hMB, hMt, hM⟩ := ih
    let A' := A.filter fun a => ∀ b ∈ M, ¬R a b
    obtain ⟨b, hb, hcover⟩ := exists_covering_vertex A' B hB R θ
      (fun a ha => hdeg a (mem_filter.mp ha).1)
    refine ⟨insert b M, insert_subset hb hMB,
      (card_insert_le _ _).trans (Nat.succ_le_succ hMt), ?_⟩
    have hfilter : (A.filter fun a => ∀ c ∈ insert b M, ¬R a c) =
        A'.filter fun a => ¬R a b := by
      ext a
      simp only [A', mem_filter, mem_insert, forall_eq_or_imp]
      tauto
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := A') (fun a => R a b)
    have hstep : ((A'.filter fun a => ¬R a b).card : ℝ) ≤ (1-θ) * A'.card := by
      have hsplit' : ((A'.filter fun a => R a b).card : ℝ) +
          ((A'.filter fun a => ¬R a b).card : ℝ) = A'.card := by exact_mod_cast hsplit
      linarith
    rw [hfilter, pow_succ]
    calc
      _ ≤ (1-θ) * A'.card := hstep
      _ ≤ (1-θ) * ((1-θ)^t * A.card) :=
        mul_le_mul_of_nonneg_left hM (by linarith)
      _ = _ := by ring

/-- Strictly reducing the real-valued uncovered bound below one gives a
dominating set with the same finite budget. -/
theorem exists_dominating_set_of_pow_lt_one {V U : Type*}
    [DecidableEq V] [DecidableEq U]
    (A : Finset V) (B : Finset U) (hB : B.Nonempty)
    (R : V → U → Prop) [DecidableRel R] (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hdeg : ∀ a ∈ A, θ * (B.card : ℝ) ≤ (B.filter (R a)).card)
    (t : ℕ) (ht : (1-θ)^t * (A.card : ℝ) < 1) :
    ∃ M : Finset U, M ⊆ B ∧ M.card ≤ t ∧ ∀ a ∈ A, ∃ b ∈ M, R a b := by
  obtain ⟨M, hMB, hMt, hM⟩ := greedy_domination A B hB R θ hθ hθ1 hdeg t
  refine ⟨M, hMB, hMt, ?_⟩
  have hz : (A.filter fun a => ∀ b ∈ M, ¬R a b).card = 0 := by
    have : ((A.filter fun a => ∀ b ∈ M, ¬R a b).card : ℝ) < 1 := hM.trans_lt ht
    have : (A.filter fun a => ∀ b ∈ M, ¬R a b).card < 1 := by exact_mod_cast this
    omega
  intro a ha
  by_contra! hn
  have : a ∈ A.filter fun a => ∀ b ∈ M, ¬R a b := mem_filter.mpr ⟨ha, hn⟩
  simp [card_eq_zero.mp hz] at this

/-- The precise logarithmic budget in Lemma `lem:dominating-set`.
Nonempty finite sides make all logarithms and the greedy choices meaningful. -/
theorem exists_dominating_set {V U : Type*} [DecidableEq V] [DecidableEq U]
    (A : Finset V) (B : Finset U) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : V → U → Prop) [DecidableRel R] (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hdeg : ∀ a ∈ A, θ * (B.card : ℝ) ≤ (B.filter (R a)).card) :
    ∃ M : Finset U, M ⊆ B ∧
      M.card ≤ ⌈log (A.card : ℝ) / (-log (1-θ))⌉₊ + 1 ∧
      ∀ a ∈ A, ∃ b ∈ M, R a b := by
  let t := ⌈log (A.card : ℝ) / (-log (1-θ))⌉₊ + 1
  apply exists_dominating_set_of_pow_lt_one A B hB R θ hθ.le hθ1.le hdeg t
  have hbase : 0 < 1-θ := by linarith
  have hlog : 0 < -log (1-θ) := by
    have := log_neg hbase (by linarith : 1-θ < 1)
    linarith
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hceil : log (A.card : ℝ) / (-log (1-θ)) < (t : ℝ) := by
    have := Nat.le_ceil (log (A.card : ℝ) / (-log (1-θ)))
    dsimp [t]
    push_cast
    linarith
  have hbudget := (div_lt_iff₀ hlog).mp hceil
  have hprod : 0 < (1-θ)^t * (A.card : ℝ) := mul_pos (pow_pos hbase _) hcard
  apply (log_lt_log_iff hprod zero_lt_one).mp
  rw [log_one, log_mul (pow_pos hbase _).ne' hcard.ne', log_pow]
  nlinarith

end HadwigerRamsey.ThomasonUpper
