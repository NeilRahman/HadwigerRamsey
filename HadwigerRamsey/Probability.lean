import Mathlib

open scoped BigOperators
open Finset Set MeasureTheory ProbabilityTheory

namespace HadwigerRamsey

variable {Ω E I : Type*} [MeasurableSpace Ω] [Fintype E] [DecidableEq E]
  [Fintype I] [DecidableEq I] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {A : E → Set Ω}

/-- At least one of a finite family of edge events occurs. -/
def Hit (A : E → Set Ω) (S : Finset E) : Set Ω := ⋃ e ∈ S, A e

omit [DecidableEq E] in
lemma measurableSet_hit (hA : ∀ e, MeasurableSet (A e)) (S : Finset E) :
    MeasurableSet (Hit A S) := by
  exact MeasurableSet.biUnion (to_countable _) (fun e _ => hA e)

omit [MeasurableSpace Ω] [DecidableEq E] in
lemma measurableSet_hit_generate (S : Finset E) (U : Set E) (hSU : ↑S ⊆ U) :
    MeasurableSet[MeasurableSpace.generateFrom {t | ∃ e ∈ U, A e = t}] (Hit A S) := by
  exact MeasurableSet.biUnion (to_countable _) (fun e he =>
    MeasurableSpace.measurableSet_generateFrom ⟨e, hSU he, rfl⟩)

omit [Fintype E] [DecidableEq E] in
lemma probability_noHit (hA : ∀ e, MeasurableSet (A e))
    (hind : iIndepSet A μ) (S : Finset E) :
    μ.real (Hit A S)ᶜ = ∏ e ∈ S, (1 - μ.real (A e)) := by
  have h := (iIndepSet_iff A μ).mp hind S
    (f := fun e => (A e)ᶜ) (fun e _ =>
      (MeasurableSpace.measurableSet_generateFrom (by simp)).compl)
  have heq : (Hit A S)ᶜ = ⋂ e ∈ S, (A e)ᶜ := by simp [Hit]
  rw [heq, measureReal_def, h, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e he
  have hc := measureReal_add_measureReal_compl (μ := μ) (hA e)
  simp only [probReal_univ] at hc
  change μ.real (A e)ᶜ = 1 - μ.real (A e)
  linarith

/-- Disjoint sets of mutually independent edge events give independent hit events. -/
lemma probability_allHits (hA : ∀ e, MeasurableSet (A e))
    (hind : iIndepSet A μ) (S : I → Finset E)
    (hS : _root_.Pairwise (fun i j => Disjoint (S i) (S j))) (t : Finset I) :
    μ.real (⋂ i ∈ t, Hit A (S i)) = ∏ i ∈ t, μ.real (Hit A (S i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hd : Disjoint (↑(S i) : Set E) (↑(t.biUnion S) : Set E) := by
      rw [Set.disjoint_left]
      intro e he het
      obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp het
      exact Finset.disjoint_left.mp (hS (ne_of_mem_of_not_mem hj hi).symm) he hej
    have hind' := hind.indep_generateFrom_of_disjoint hA (↑(S i)) (↑(t.biUnion S)) hd
    have hm1 := measurableSet_hit_generate (A := A) (S i) (↑(S i)) (fun _ h => h)
    have hm2 : MeasurableSet[MeasurableSpace.generateFrom
        {u | ∃ e ∈ (↑(t.biUnion S) : Set E), A e = u}] (⋂ j ∈ t, Hit A (S j)) := by
      apply MeasurableSet.biInter (to_countable _)
      intro j hj
      exact measurableSet_hit_generate (S j) _ (fun e he => mem_biUnion.mpr ⟨j,hj,he⟩)
    have hm := (hind'.indepSet_of_measurableSet hm1 hm2).measure_inter_eq_mul
    simp only [Finset.set_biInter_insert, Finset.prod_insert hi]
    rw [measureReal_def, hm, ENNReal.toReal_mul]
    change μ.real (Hit A (S i)) * μ.real (⋂ j ∈ t, Hit A (S j)) = _
    rw [ih]

end HadwigerRamsey
