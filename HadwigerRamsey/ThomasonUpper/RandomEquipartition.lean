import HadwigerRamsey.ThomasonUpper.CompleteEquipartition
import HadwigerRamsey.ThomasonUpper.FiniteExpectations

open scoped BigOperators Classical ENNReal
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- The final probabilistic and deletion argument for A.1. The inputs
are the unacceptable-part bound r and the acceptable defective-pair bound P.
The conclusion has exactly the manuscript's two factors of four. -/
theorem complete_equipartition_of_probability_bounds {Ω V : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {s L : ℕ} (hs : 0 < s) (hL : 0 < L)
    (W : Ω → Fin s → Finset V)
    (hcard : ∀ p i, (W p i).card = L)
    (hdisj : ∀ p, Pairwise (fun i j => Disjoint (W p i) (W p j)))
    (ok : Fin s → Set Ω) {r P : ℝ} (hr : 0 < r) (hP : 0 < P)
    (hbad : ∀ i, ((PMF.uniformOfFintype Ω).toOuterMeasure (ok i)ᶜ).toReal ≤ r)
    (hpair : ∀ i j, i ≠ j →
      ((PMF.uniformOfFintype Ω).toOuterMeasure
        {p | p ∈ ok i ∧ p ∈ ok j ∧ ¬PartsJoined G (W p i) (W p j)}).toReal ≤ P) :
    ∃ m : ℕ, ∃ U : Fin m → Finset V, 0 < m ∧ m ≤ s ∧
      (s : ℝ)-4*s*r-4*(s : ℝ)^2*P ≤ m ∧ IsCompleteEquipartition G U := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases hsmall : (s : ℝ)-4*s*r-4*(s : ℝ)^2*P ≤ 1
  · let p0 : Ω := Classical.choice inferInstance
    let i0 : Fin s := ⟨0,hs⟩
    have hne : (W p0 i0).Nonempty := card_pos.mp (by rw [hcard]; exact hL)
    letI : Nonempty V := ⟨hne.choose⟩
    refine ⟨1,fun _ => univ,by omega,by omega,by simpa using hsmall,?_,?_,?_,?_,?_⟩
    · intro i
      exact univ_nonempty
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))
    · intro v
      exact ⟨0,mem_univ v⟩
    · intro i j
      omega
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))
  · let bad := fun i => (ok i)ᶜ
    let defEvent := fun e : Fin s × Fin s =>
      {p | p ∈ ok e.1 ∧ p ∈ ok e.2 ∧ ¬PartsJoined G (W p e.1) (W p e.2)}
    let Ucount := fun p => (occurringEvents univ bad p).card
    let Zcount := fun p => (occurringEvents univ.offDiag defEvent p).card
    have hEU : (𝔼 p, (Ucount p : ℝ)) ≤ (s : ℝ)*r := by
      change (𝔼 p, ((occurringEvents univ bad p).card : ℝ)) ≤ _
      rw [expected_occurringEvents]
      calc
        _ ≤ ∑ _i : Fin s, r := sum_le_sum (fun i _ => hbad i)
        _ = _ := by simp
    have hEZ : (𝔼 p, (Zcount p : ℝ)) ≤ (s : ℝ)^2*P := by
      change (𝔼 p, ((occurringEvents univ.offDiag defEvent p).card : ℝ)) ≤ _
      rw [expected_occurringEvents]
      have hc : (univ.offDiag : Finset (Fin s × Fin s)).card ≤ s*s := by
        simpa using card_le_univ (univ.offDiag : Finset (Fin s × Fin s))
      calc
        _ ≤ ∑ _e ∈ (univ.offDiag : Finset (Fin s × Fin s)), P := by
          apply sum_le_sum
          intro e he
          exact hpair e.1 e.2 (mem_offDiag.mp he).2.2
        _ = (univ.offDiag : Finset (Fin s × Fin s)).card*P := by simp
        _ ≤ _ := by
          have hcR : ((univ.offDiag : Finset (Fin s × Fin s)).card : ℝ) ≤ (s : ℝ)^2 := by
            exact_mod_cast (by simpa only [pow_two] using hc : (univ.offDiag : Finset (Fin s × Fin s)).card ≤ s^2)
          exact mul_le_mul_of_nonneg_right hcR hP.le
    obtain ⟨p,hU,hZ⟩ := exists_simultaneous_four_bounds
      (fun p => (Ucount p : ℝ)) (fun p => (Zcount p : ℝ))
      (mul_pos hsR hr) (mul_pos (sq_pos_of_pos hsR) hP)
      (fun _ => by positivity) (fun _ => by positivity) hEU hEZ
    let A := univ.filter (fun i => p ∈ ok i)
    have hA : A.card+Ucount p = s := by
      have hh := card_filter_add_card_filter_not (s := (univ : Finset (Fin s)))
        (p := fun i => p ∈ ok i)
      simpa only [A,Ucount,occurringEvents,bad,Set.mem_compl_iff,card_univ,Fintype.card_fin] using hh
    have hAreal : (A.card : ℝ)+(Ucount p : ℝ) = s := by exact_mod_cast hA
    have hdef : ((A ×ˢ A).filter (fun e => e.1 ≠ e.2 ∧ ¬PartsJoined G (W p e.1) (W p e.2))) =
        occurringEvents univ.offDiag defEvent p := by
      ext e
      simp only [A,defEvent,occurringEvents,mem_filter,mem_product,mem_univ,true_and,mem_offDiag,Set.mem_ofPred_eq]
      tauto
    have hpos : 4*(s : ℝ)^2*P < (A.card : ℝ) := by
      push Not at hsmall
      nlinarith
    obtain ⟨m,Q,hm,hms,hlower,hQ⟩ := complete_equipartition_after_defects G (W p) hL
      (hcard p) (hdisj p) A (b := 4*(s : ℝ)^2*P) (by rw [hdef]; change (Zcount p : ℝ) ≤ _; nlinarith [hZ]) hpos
    refine ⟨m,Q,hm,hms,?_,hQ⟩
    nlinarith

end HadwigerRamsey.ThomasonUpper
