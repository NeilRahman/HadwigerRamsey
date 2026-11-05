import HadwigerRamsey4Col.TriangleReduction
import HadwigerRamsey4Col.FixedPattern

open Real Finset
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
namespace HadwigerRamsey4Col
namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β]

/-- The lower bound holds for arbitrary finite component programs. -/
theorem lower_bound (P : FiniteProgram α β) : tStar parameter ≤ P.bound := by
  by_cases ht : P.bound ≤ threshold
  · let Q := P.merge
    have hQ : Q.bound ≤ threshold := ht
    have hinj : Function.Injective Q.word := P.merge_word_injective
    rcases Q.patterns with hfix | hball | htriangle
    · obtain ⟨c,d,hcd,b,e,hfixed⟩ := hfix
      exact (Q.no_two_fixed hQ c d hcd b e
        (fun i => (hfixed _ ⟨i,rfl⟩).1) (fun i => (hfixed _ ⟨i,rfl⟩).2)).elim
    · obtain ⟨z,hz⟩ := hball
      exact (Q.no_ball hQ hinj z (fun i => hz _ ⟨i,rfl⟩)).elim
    · obtain ⟨σ,hσ,a,b,c,d,e,f,g,hab,hcd,hef,hwords⟩ := htriangle
      let E : Equiv.Perm (Fin 4) := Equiv.ofBijective σ hσ
      let R := Q.recolour E
      have hR : R.bound ≤ threshold := hQ
      have hInj : Function.Injective R.word := by
        intro i j hij
        apply hinj
        funext c
        obtain ⟨d,rfl⟩ := E.surjective c
        exact congrFun hij d
      apply R.triangle_lower_bound hR hInj a b c d e f g hab hcd hef
      intro i
      have hh := hwords _ ⟨i,rfl⟩
      rcases hh with hh | hh | hh | hh
      · exact ⟨0,hh⟩
      · exact ⟨1,hh⟩
      · exact ⟨2,hh⟩
      · exact ⟨3,hh⟩
  · exact (tStar_lt_threshold parameter_spec.1 parameter_spec.2.2).le.trans (le_of_not_ge ht)

end FiniteProgram

/-- Every feasible instance of the original four-colour program has this lower bound. -/
theorem instance_lower_bound (I : ComponentInstance) : sqrt (tStar parameter) ≤ I.objective := by
  let : Nonempty (Fin I.k) := ⟨⟨0,I.k_pos⟩⟩
  have hh := (instanceProgram I).lower_bound
  change tStar parameter ≤ I.objective^2 at hh
  have hn : 0 ≤ I.objective := le_trans (by norm_num : (0:ℝ)≤(4:ℝ)⁻¹)
    (I.inv_colors_le_objective (by norm_num))
  exact (sqrt_le_iff).mpr ⟨hn,hh⟩

/-- Exact value of the four-colour component program's square-root objective. -/
theorem beta4_eq : beta4 = sqrt (tStar parameter) := by
  apply le_antisymm beta4_upper
  apply le_csInf
  · exact ⟨_,⟨attainingInstance,rfl⟩⟩
  · rintro _ ⟨I,rfl⟩
    exact instance_lower_bound I

/-- The specified four equal atoms attain the infimum. -/
theorem optimum_attained : attainingInstance.objective=beta4 :=
  attaining_objective.trans beta4_eq.symm

/-- Theorem 1: the exact optimum and its attaining four-atom construction.
The construction's masses, partitions, diagonal and off-diagonal probabilities
are given explicitly by `attainingInstance`, `optimalLabel`, and `optimalDensity`. -/
theorem theorem1 {p : ℝ} (hp : 0<p ∧ p<1 ∧ 3*p^6+2*p-2=0) :
    beta4^2=-(3/4 : ℝ)*log p ∧ attainingInstance.objective=beta4 := by
  have he : p=parameter := ExistsUnique.unique exists_unique_parameter hp parameter_spec
  subst p
  refine ⟨?_,optimum_attained⟩
  rw [beta4_eq,sq_sqrt tStar_pos.le]
  rfl

end HadwigerRamsey4Col
