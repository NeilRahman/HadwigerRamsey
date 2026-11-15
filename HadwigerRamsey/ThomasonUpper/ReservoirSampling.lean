import HadwigerRamsey.ThomasonUpper.RandomLabels
import HadwigerRamsey.ThomasonUpper.Concentration
import HadwigerRamsey.ThomasonUpper.IndependentBlocks
import HadwigerRamsey.ThomasonUpper.ShortPaths

open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory Real

namespace HadwigerRamsey.ThomasonUpper

theorem eventCount_label_eq {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (a : Option Bool) (ω : V → Option Bool) :
    eventCount (fun v => {ω : V → Option Bool | ω v = a}) S ω =
      ((S.filter fun v => ω v = a).card : ℝ) := by
  classical
  simp [eventCount, Set.indicator_apply]

/-- Lemma A.4's reservoir-size tail, using Hoeffding in place of Chernoff. -/
theorem label_count_upper {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) (S : Finset V) (b : Bool) :
    (randomLabels r hr hrhalf).real
      {ω | 2*r*S.card ≤ ((S.filter fun v => ω v = some b).card : ℝ)} ≤
      exp (-2*r^2*S.card) := by
  classical
  let A := fun v : V => {ω : V → Option Bool | ω v = some b}
  have hA : ∀ v, MeasurableSet (A v) := fun v =>
    (measurable_pi_apply v) (measurableSet_singleton _)
  have hmean : (∑ v ∈ S, (randomLabels r hr hrhalf).real (A v)) = r*S.card := by
    simp [A, randomLabels_probability_label, mul_comm]
  have hh := eventCount_upper_tail (randomLabels r hr hrhalf) A hA
    (randomLabels_independent r hr hrhalf (some b)) S (t := r*S.card) (by positivity)
  have he : {ω | (∑ v ∈ S, (randomLabels r hr hrhalf).real (A v)) + r*S.card ≤ eventCount A S ω} =
      {ω | 2*r*S.card ≤ ((S.filter fun v => ω v = some b).card : ℝ)} := by
    ext ω
    rw [hmean]
    change (r*S.card+r*S.card ≤ eventCount (fun v => {ω : V → Option Bool | ω v = some b}) S ω) ↔ _
    rw [eventCount_label_eq]
    change (r*S.card+r*S.card ≤ ((S.filter fun v => ω v = some b).card : ℝ)) ↔
      (2*r*S.card ≤ ((S.filter fun v => ω v = some b).card : ℝ))
    constructor <;> intro h <;> linarith
  rw [he] at hh
  convert hh using 1
  congr 1
  by_cases hs : S.card = 0
  · simp [hs]
  · have hsR : (S.card : ℝ) ≠ 0 := by exact_mod_cast hs
    field_simp

/-- Lemma A.4's neighbor-count tail for an arbitrary fixed vertex set. -/
theorem label_count_lower {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) (S : Finset V) (b : Bool) :
    (randomLabels r hr hrhalf).real
      {ω | ((S.filter fun v => ω v = some b).card : ℝ) ≤ r*S.card/2} ≤
      exp (-r^2*S.card/2) := by
  classical
  have hh := eventCount_below_half (randomLabels r hr hrhalf)
    (fun v : V => {ω : V → Option Bool | ω v = some b})
    (fun v => (measurable_pi_apply v) (measurableSet_singleton _))
    (randomLabels_independent r hr hrhalf (some b)) S hr
    (fun v _ => by simp [randomLabels_probability_label])
  simpa only [eventCount_label_eq] using hh

/-- The number of short, internally disjoint candidate paths surviving
in C has a uniform exponential lower-tail estimate. -/
theorem path_survival_lower {n H : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : u ≠ v) (P : Finset (G.Path u v))
    (hd : (P : Set (G.Path u v)).PairwiseDisjoint pathInterior)
    (hlen : ∀ p ∈ P, p.val.length ≤ H)
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    (randomLabels r hr hrhalf).real
      {ω | ((P.filter fun p => ∀ x ∈ pathInterior p, ω x = some true).card : ℝ) ≤
        r^(H-1)*P.card/2} ≤ exp (-(r^(H-1))^2*P.card/2) := by
  classical
  let A := fun x : Fin n => {ω : Fin n → Option Bool | ω x = some true}
  let E := fun p : P => allIn A (pathInterior p.val)
  have hA : ∀ x, MeasurableSet (A x) := fun x =>
    (measurable_pi_apply x) (measurableSet_singleton _)
  have hind : iIndepSet E (randomLabels r hr hrhalf) :=
    independent_allIn _ A hA (randomLabels_independent r hr hrhalf (some true))
      (fun p : P => pathInterior p.val) (by
        intro p q hpq
        exact hd p.property q.property (fun h => hpq (Subtype.ext h)))
  have hprob : ∀ p : P, r^(H-1) ≤ (randomLabels r hr hrhalf).real (E p) := by
    intro p
    have he := probability_allIn (randomLabels r hr hrhalf) A hA
      (randomLabels_independent r hr hrhalf (some true)) (pathInterior p.val)
      (r := r) (fun x _ => by simp [A, randomLabels_probability_label])
    rw [he]
    apply pow_le_pow_of_le_one hr (by linarith : r ≤ 1)
    have hc := pathInterior_card huv p.val
    have hl := hlen p.val p.property
    omega
  have hh := eventCount_below_half (randomLabels r hr hrhalf) E
    (fun p => measurableSet_allIn A hA _) hind univ
    (q := r^(H-1)) (by positivity) (fun p _ => hprob p)
  have he : ∀ ω, eventCount E univ ω =
      ((P.filter fun p => ∀ x ∈ pathInterior p, ω x = some true).card : ℝ) := by
    intro ω
    simp only [eventCount, E, allIn, Set.indicator_apply, Set.mem_iInter]
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    norm_cast
    apply card_bij (fun p _ => p.val)
    · intro p hp
      exact mem_filter.mpr ⟨p.property, (mem_filter.mp hp).2⟩
    · intro p _ q _ h
      exact Subtype.ext h
    · intro p hp
      exact ⟨⟨p,(mem_filter.mp hp).1⟩, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩, rfl⟩
  simpa only [he, card_univ, Fintype.card_coe] using hh

end HadwigerRamsey.ThomasonUpper
