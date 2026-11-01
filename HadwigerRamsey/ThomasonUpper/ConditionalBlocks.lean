import HadwigerRamsey.ThomasonUpper.FiniteProbabilityFibers
import HadwigerRamsey.ThomasonUpper.UniformInstances

open scoped BigOperators Classical ENNReal
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- A uniform conditional bound for a second part, proved by summing
exact joint probabilities over the first vector. The acceptable first
vectors may be selected by any predicate C. -/
theorem acceptable_second_part_probability {I : Type*} [Fintype I] [DecidableEq I] {s : ℕ}
    (hs : 0 < s) (t u : Fin s) (htu : t ≠ u)
    (C : (I → Fin s) → Prop) (T : (I → Fin s) → I → Finset (Fin s))
    {P : ℝ} (hP : 0 ≤ P) (hexclude : ∀ x i, x i ∉ T x i)
    (hproduct : ∀ x, C x → (∏ i, ((T x i).card : ℝ)/((s : ℝ)-1)) ≤ P) :
    ((PMF.uniformOfFintype (I → Equiv.Perm (Fin s))).toOuterMeasure
      {p | C (fun i => p i t) ∧ ∀ i, p i u ∈ T (fun i => p i t) i}).toReal ≤ P := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  let A : Set (I → Equiv.Perm (Fin s)) :=
    {p | C (fun i => p i t) ∧ ∀ i, p i u ∈ T (fun i => p i t) i}
  have hbase : 0 ≤ (1/(s : ℝ))^(Fintype.card I) := by positivity
  have hterm : ∀ x : I → Fin s,
      ((PMF.uniformOfFintype (I → Equiv.Perm (Fin s))).toOuterMeasure
        {p | (fun i => p i t) = x ∧ p ∈ A}).toReal ≤
          (1/(s : ℝ))^(Fintype.card I)*P := by
    intro x
    by_cases hx : C x
    · have hsub : {p : I → Equiv.Perm (Fin s) | (fun i => p i t) = x ∧ p ∈ A} ⊆
        {p | ∀ i, p i t = x i ∧ p i u ∈ T x i} := by
        intro p hp
        intro i
        exact ⟨congrFun hp.1 i,by simpa only [← hp.1] using hp.2.2 i⟩
      exact (uniform_probability_mono hsub).trans
        ((uniform_block_pair_event_real_of_fintype _ t u htu x (T x) (hexclude x)).le.trans
          (mul_le_mul_of_nonneg_left (hproduct x hx) hbase))
    · have he : {p : I → Equiv.Perm (Fin s) | (fun i => p i t) = x ∧ p ∈ A} = ∅ := by
        ext p
        simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
        intro hp
        intro hA
        exact hx (hp ▸ hA.1)
      rw [he]
      simpa using mul_nonneg hbase hP
  have hsum := sum_le_sum (s := univ) (fun x _ => hterm x)
  rw [← uniform_probability_sum_fibers (fun p i => p i t) A] at hsum
  have hnorm : (∑ _x : I → Fin s, (1/(s : ℝ))^(Fintype.card I)*P) = P := by
    simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [one_div,inv_pow]
    field_simp
  exact hsum.trans_eq hnorm

end HadwigerRamsey.ThomasonUpper
