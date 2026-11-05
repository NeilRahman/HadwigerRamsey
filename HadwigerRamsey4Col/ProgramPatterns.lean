import HadwigerRamsey4Col.Program
import HadwigerRamsey4Col.Patterns

open scoped BigOperators
namespace HadwigerRamsey4Col

/-- Feasibility forces at least two available colours between any two atoms. -/
theorem component_words_close (I : ComponentInstance) (i j : Fin I.k) :
    hammingDist (fun c => I.label c i) (fun c => I.label c j) ≤ 2 := by
  apply (near_iff_hamming _ _).mp
  by_contra hn
  have hs := I.density_sum i j
  simp [Fin.sum_univ_succ] at hs
  have h0 := I.density_lt_one 0 i j
  have h1 := I.density_lt_one 1 i j
  have h2 := I.density_lt_one 2 i j
  have h3 := I.density_lt_one 3 i j
  have z0 := I.density_zero 0 i j
  have z1 := I.density_zero 1 i j
  have z2 := I.density_zero 2 i j
  have z3 := I.density_zero 3 i j
  unfold Near at hn
  grind

/-- Lemma 2 applied to the component-label words of an actual program instance. -/
theorem component_pattern_classification (I : ComponentInstance) :
    PatternFamily (Set.range (fun i : Fin I.k => fun c => I.label c i)) := by
  let : NeZero I.k := ⟨ne_of_gt I.k_pos⟩
  apply lemma2
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
  exact component_words_close I i j

end HadwigerRamsey4Col
