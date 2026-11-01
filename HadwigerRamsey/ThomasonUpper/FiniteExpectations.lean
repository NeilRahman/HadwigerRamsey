import Mathlib

open scoped BigOperators Classical ENNReal
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- A uniform finite event probability equals the finite expectation of
its indicator. Both objects use Mathlib's existing definitions. -/
theorem uniform_probability_eq_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (A : Set Ω) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure A).toReal =
      𝔼 ω, (if ω ∈ A then (1 : ℝ) else 0) := by
  classical
  rw [PMF.uniformOfFintype,PMF.toOuterMeasure_uniformOfFinset_apply,
    ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast,
    Fintype.expect_eq_sum_div_card]
  simp

/-- Linearity of expectation for the number of events that occur. -/
theorem expected_event_count {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty Ω]
    (A : I → Set Ω) :
    (𝔼 ω, ((univ.filter (fun i => ω ∈ A i)).card : ℝ)) =
      ∑ i, ((PMF.uniformOfFintype Ω).toOuterMeasure (A i)).toReal := by
  classical
  have hc : ∀ ω, ((univ.filter (fun i => ω ∈ A i)).card : ℝ) =
      ∑ i, if ω ∈ A i then (1 : ℝ) else 0 := by
    intro ω
    simp
  simp_rw [hc,uniform_probability_eq_expect]
  exact expect_sum_comm _ _ _

/-- The same linearity formula restricted to any finite vertex set. -/
theorem expected_finset_event_count {V Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Finset V) (A : V → Set Ω) :
    (𝔼 ω, ((S.filter (fun v => ω ∈ A v)).card : ℝ)) =
      ∑ v ∈ S, ((PMF.uniformOfFintype Ω).toOuterMeasure (A v)).toReal := by
  classical
  have hc : ∀ ω, ((S.filter (fun v => ω ∈ A v)).card : ℝ) =
      ∑ v ∈ S, if ω ∈ A v then (1 : ℝ) else 0 := by
    intro ω
    simp
  simp_rw [hc,uniform_probability_eq_expect]
  exact expect_sum_comm _ _ _

/-- A fixed finite-event counting function, with its membership
predicate kept abstract to avoid recomputing finite decision procedures. -/
noncomputable def occurringEvents {I Ω : Type*} (S : Finset I) (A : I → Set Ω)
    (p : Ω) : Finset I := S.filter (fun i => p ∈ A i)

theorem expected_occurringEvents {I Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Finset I) (A : I → Set Ω) :
    (𝔼 p, ((occurringEvents S A p).card : ℝ)) =
      ∑ i ∈ S, ((PMF.uniformOfFintype Ω).toOuterMeasure (A i)).toReal :=
  expected_finset_event_count S A

/-- Markov's inequality for a finite uniform sample, in the strict
threshold form used to define rejected blocks. -/
theorem uniform_markov {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {a : ℝ} (ha : 0 < a) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | a < f ω}).toReal ≤
      (𝔼 ω, f ω)/a := by
  rw [uniform_probability_eq_expect]
  calc
    _ ≤ 𝔼 ω, f ω/a := by
      apply expect_le_expect
      intro ω hω
      by_cases h : a < f ω
      · simp only [Set.mem_ofPred_eq,h,if_true]
        exact (le_div_iff₀ ha).mpr (by linarith)
      · simp only [Set.mem_ofPred_eq,h,if_false]
        exact div_nonneg (hf ω) ha.le
    _ = _ := (expect_div _ _ _).symm

/-- A block whose expected count is at most c is rejected at the
threshold omega*c with probability at most 1/omega. -/
theorem rejected_block_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {c omega : ℝ}
    (hc : 0 < c) (homega : 0 < omega) (hmean : (𝔼 ω, f ω) ≤ c) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | omega*c < f ω}).toReal ≤ 1/omega := by
  have hh := (uniform_markov f hf (mul_pos homega hc)).trans
    (div_le_div_of_nonneg_right hmean (mul_pos homega hc).le)
  have heq : c/(omega*c) = 1/omega := by field_simp
  exact hh.trans_eq heq

/-- If at most ell blocks are individually rejected with probability
at most 1/omega, the probability of more than phi*ell rejections is at
most 1/(omega*phi), as in equation unacceptable-prob. -/
theorem unacceptable_probability {I Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Finset I) (rejected : I → Set Ω) {ell : ℕ} {omega phi : ℝ}
    (homega : 0 < omega) (hphi : 0 < phi) (hell : 0 < ell)
    (hcard : E.card ≤ ell)
    (hprob : ∀ i ∈ E, ((PMF.uniformOfFintype Ω).toOuterMeasure (rejected i)).toReal ≤ 1/omega) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure
      {ω | phi*(ell : ℝ) < ((E.filter (fun i => ω ∈ rejected i)).card : ℝ)}).toReal ≤
      1/(omega*phi) := by
  have hcount : (𝔼 ω, ((E.filter (fun i => ω ∈ rejected i)).card : ℝ)) ≤ (ell : ℝ)/omega := by
    rw [expected_finset_event_count]
    calc
      _ ≤ ∑ _i ∈ E, 1/omega := sum_le_sum hprob
      _ = (E.card : ℝ)/omega := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) homega.le
  have hpos : 0 < phi*(ell : ℝ) := mul_pos hphi (by exact_mod_cast hell)
  have hh := (uniform_markov (fun ω => ((E.filter (fun i => ω ∈ rejected i)).card : ℝ))
    (fun ω => by positivity) hpos).trans
      (div_le_div_of_nonneg_right hcount hpos.le)
  have heq : ((ell : ℝ)/omega)/(phi*(ell : ℝ)) = 1/(omega*phi) := by
    have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
    field_simp
  exact hh.trans_eq heq

/-- Two nonnegative counts have simultaneous four-times-expectation
bounds. A single application of Mathlib's finite averaging principle to
their normalized sum proves the same bounds as the Markov/union step. -/
theorem exists_simultaneous_four_bounds {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (U Z : Ω → ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hU : ∀ ω, 0 ≤ U ω) (hZ : ∀ ω, 0 ≤ Z ω)
    (hEU : (𝔼 ω, U ω) ≤ A) (hEZ : (𝔼 ω, Z ω) ≤ B) :
    ∃ ω, U ω ≤ 4*A ∧ Z ω ≤ 4*B := by
  have hmean : (𝔼 ω, (U ω/A+Z ω/B)) ≤ 2 := by
    rw [expect_add_distrib,← expect_div,← expect_div]
    have hu : (𝔼 ω, U ω)/A ≤ 1 := (div_le_iff₀ hA).mpr (by simpa using hEU)
    have hz : (𝔼 ω, Z ω)/B ≤ 1 := (div_le_iff₀ hB).mpr (by simpa using hEZ)
    linarith
  obtain ⟨ω,hω,hbound⟩ := exists_le_of_expect_le univ_nonempty hmean
  refine ⟨ω,?_,?_⟩
  · have hz := div_nonneg (hZ ω) hB.le
    have hu : U ω/A ≤ 4 := by linarith
    exact (div_le_iff₀ hA).mp hu
  · have hu := div_nonneg (hU ω) hA.le
    have hz : Z ω/B ≤ 4 := by linarith
    exact (div_le_iff₀ hB).mp hz

end HadwigerRamsey.ThomasonUpper
