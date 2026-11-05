import HadwigerRamsey4Col.ReindexProgram

open Real Finset
open scoped BigOperators Classical
namespace HadwigerRamsey4Col
namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma ball_other_coordinate (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (i : α) (c d : Fin 4)
    (hc : P.label c i ≠ z c) (hcd : c ≠ d) : P.label d i=z d := by
  have hh := hball i
  unfold BallNear word at hh
  fin_cases c <;> fin_cases d <;> norm_num at hcd <;> grind

lemma exists_different_coordinate (P : FiniteProgram α β) (z : Word β) (i : α)
    (h : P.word i ≠ z) : ∃ c, P.label c i ≠ z c := by
  by_contra! hn
  exact h (funext hn)

noncomputable def ballClass (P : FiniteProgram α β) (z : Word β) (i : α) : Option (Fin 4) :=
  if h : P.word i=z then none else some (Classical.choose (P.exists_different_coordinate z i h))

@[simp] lemma ballClass_none (P : FiniteProgram α β) (z : Word β) (i : α) :
    P.ballClass z i=none ↔ P.word i=z := by
  unfold ballClass
  split_ifs <;> simp_all

lemma ballClass_some (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (i : α) (c : Fin 4) :
    P.ballClass z i=some c ↔ P.label c i ≠ z c := by
  unfold ballClass
  split_ifs with he
  · have hc : P.label c i=z c := congrFun he c
    simp [hc]
  · have hx := Classical.choose_spec (P.exists_different_coordinate z i he)
    simp only [Option.some.injEq]
    constructor
    · intro h
      simpa only [h] using hx
    · intro hc
      by_contra hd
      exact hc (P.ball_other_coordinate z hball i _ c hx hd)

lemma ballClass_ne_some (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (i : α) (c : Fin 4) :
    P.ballClass z i ≠ some c ↔ P.label c i=z c := by
  exact (not_congr (P.ballClass_some z hball i c)).trans (not_not)

lemma ball_nonmain_zero (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (i j : α) (hij : i ≠ j) (c : Fin 4)
    (hn : P.ballClass z i=some c ∨ P.ballClass z j=some c) : P.density c i j=0 := by
  apply P.density_zero c i j
  intro he
  have hi : P.label c i ≠ z c := by
    rcases hn with hn | hn
    · exact (P.ballClass_some z hball i c).mp hn
    · rw [he]
      exact (P.ballClass_some z hball j c).mp hn
  have hj : P.label c j ≠ z c := by rwa [← he]
  apply hij
  apply hinj
  funext d
  by_cases hd : d=c
  · subst d
    exact he
  · exact (P.ball_other_coordinate z hball i c d hi (Ne.symm hd)).trans
      (P.ball_other_coordinate z hball j c d hj (Ne.symm hd)).symm

lemma ball_singleton_part (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (i : α) (c : Fin 4) (hi : P.ballClass z i=some c) :
    P.part c (P.label c i) = {i} := by
  ext j
  simp only [part, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro hj
    apply hinj
    funext d
    by_cases hd : d=c
    · subst d
      exact hj
    · have hi' := (P.ballClass_some z hball i c).mp hi
      have hj' : P.label c j ≠ z c := by rwa [hj]
      exact (P.ball_other_coordinate z hball j c d hj' (Ne.symm hd)).trans
        (P.ball_other_coordinate z hball i c d hi' (Ne.symm hd)).symm
  · rintro rfl
    rfl

noncomputable def classMass (P : FiniteProgram α β) (z : Word β) (u : Option (Fin 4)) : ℝ :=
  ∑ i with P.ballClass z i=u, P.mass i

lemma classMass_nonneg (P : FiniteProgram α β) (z : Word β) (u : Option (Fin 4)) :
    0 ≤ P.classMass z u := sum_nonneg (fun i _ => P.mass_nonneg i)

lemma classMass_sum (P : FiniteProgram α β) (z : Word β) :
    P.classMass z none+(∑ c, P.classMass z (some c))=1 := by
  have hh := sum_fiberwise univ (P.ballClass z) P.mass
  simpa [classMass, Fintype.sum_option] using hh.trans P.mass_sum

lemma ball_main_mass (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (c : Fin 4) :
    P.partMass c (z c) = 1-P.classMass z (some c) := by
  have he : (∑ i, if P.label c i=z c then P.mass i else 0)+
      (∑ i, if P.label c i≠z c then P.mass i else 0)=1 := by
    rw [← sum_add_distrib]
    convert P.mass_sum using 1
    apply sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  have hc : P.classMass z (some c) = ∑ i, if P.label c i≠z c then P.mass i else 0 := by
    simp only [classMass, sum_filter, P.ballClass_some z hball]
  rw [hc]
  dsimp [partMass,regionMass,part]
  simp only [sum_filter]
  linarith

end FiniteProgram
end HadwigerRamsey4Col
