import HadwigerRamsey.Finite

open scoped BigOperators
open Finset Set MeasureTheory ProbabilityTheory
namespace HadwigerRamsey

/-- Any graph property is measurable when all the finitely many edge events are. -/
lemma measurableSet_graph_property {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (G : Ω → SimpleGraph (Fin n)) (hA : ∀ e, MeasurableSet (edgeEvent G e))
    (P : SimpleGraph (Fin n) → Prop) : MeasurableSet {ω | P (G ω)} := by
  classical
  have heq : ∀ H : SimpleGraph (Fin n), MeasurableSet {ω | G ω = H} := by
    intro H
    have hset : {ω | G ω = H} = ⋂ e : Edge n,
        (if H.Adj e.val.1 e.val.2 then edgeEvent G e else (edgeEvent G e)ᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h e
        subst H
        by_cases he : (G ω).Adj e.val.1 e.val.2 <;> simp [he, edgeEvent]
      · intro h
        apply SimpleGraph.ext
        funext u v
        apply propext
        by_cases huv : u = v
        · subst v; simp
        · rcases lt_or_gt_of_ne huv with hlt | hgt
          · have he := h ⟨(u,v), hlt⟩
            by_cases heH : H.Adj u v <;> simp [heH, edgeEvent] at he ⊢ <;> exact he
          · have he := h ⟨(v,u), hgt⟩
            by_cases heH : H.Adj v u
            · simp only [heH, ite_true, edgeEvent, mem_setOf_eq] at he
              exact ⟨fun _ => heH.symm, fun _ => he.symm⟩
            · simp only [heH, ite_false, mem_compl_iff, edgeEvent, mem_setOf_eq] at he
              exact ⟨fun hh => (he hh.symm).elim, fun hh => (heH hh.symm).elim⟩
    rw [hset]
    apply MeasurableSet.iInter
    intro e
    split_ifs
    · exact hA e
    · exact (hA e).compl
  have hset : {ω | P (G ω)} = ⋃ H : SimpleGraph (Fin n),
      (if P H then {ω | G ω = H} else ∅) := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro h
      exact ⟨G ω, by simp [h]⟩
    · rintro ⟨H,hH⟩
      split_ifs at hH with hp
      · exact hH.symm ▸ hp
      · exact hH.elim
  rw [hset]
  apply MeasurableSet.iUnion
  intro H
  split_ifs
  · exact heq H
  · exact MeasurableSet.empty

end HadwigerRamsey
