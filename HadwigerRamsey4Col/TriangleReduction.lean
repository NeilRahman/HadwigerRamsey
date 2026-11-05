import HadwigerRamsey4Col.BallExclusion
import HadwigerRamsey4Col.PairingReduction

open Real Finset
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
namespace HadwigerRamsey4Col

noncomputable def triangleWord {β : Type} (a b c d e f g : β) : Fin 4 → Word β :=
  ![![a,c,e,g],![a,d,f,g],![b,c,f,g],![b,d,e,g]]
noncomputable def triangleCentre {β : Type} (a b c d e f g : β) : Fin 4 → Word β :=
  ![![b,d,f,g],![b,c,e,g],![a,d,e,g],![a,c,f,g]]

lemma triangleWord_injective {β : Type} (a b c d e f g : β)
    (hab : a≠b) (hcd : c≠d) (_hef : e≠f) : Function.Injective (triangleWord a b c d e f g) := by
  intro k l he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  fin_cases k <;> fin_cases l <;> norm_num [triangleWord] at h0 h1 h2 ⊢ <;> grind

lemma triangleWord_near_centre {β : Type} (a b c d e f g : β) (k l : Fin 4) (hkl : k≠l) :
    BallNear (triangleWord a b c d e f g l) (triangleCentre a b c d e f g k) := by
  fin_cases k <;> fin_cases l <;> norm_num [Fin.ext_iff] at hkl <;>
    simp [triangleWord,triangleCentre,BallNear]

namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma triangle_lower_bound (P : FiniteProgram α β) (ht : P.bound ≤ threshold)
    (hinj : Function.Injective P.word) (a b c d e f g : β)
    (hab : a≠b) (hcd : c≠d) (hef : e≠f)
    (hcover : ∀ i, ∃ k,P.word i=triangleWord a b c d e f g k) : tStar parameter ≤ P.bound := by
  have hfull : ∀ k, ∃ i,P.word i=triangleWord a b c d e f g k := by
    intro k
    by_contra hn
    apply P.no_ball ht hinj (triangleCentre a b c d e f g k)
    intro i
    obtain ⟨l,hl⟩ := hcover i
    rw [hl]
    apply triangleWord_near_centre
    intro h
    subst l
    exact hn ⟨i,hl⟩
  let eAtom : Fin 4 → α := fun k => Classical.choose (hfull k)
  have heWord (k) : P.word (eAtom k)=triangleWord a b c d e f g k := Classical.choose_spec (hfull k)
  have heInj : Function.Injective eAtom := by
    intro k l h
    apply triangleWord_injective a b c d e f g hab hcd hef
    rw [← heWord k,← heWord l,h]
  have heSurj : Function.Surjective eAtom := by
    intro i
    obtain ⟨k,hk⟩ := hcover i
    exact ⟨k,hinj ((heWord k).trans hk.symm)⟩
  let E : Fin 4 ≃ α := Equiv.ofBijective eAtom ⟨heInj,heSurj⟩
  let Q := P.reindex E
  have hlabel (col i) : Q.label col i=triangleWord a b c d e f g i col := congrFun (heWord i) col
  have hpattern : ∀ c i j,Q.label c i=Q.label c j ↔ optimalLabel c i=optimalLabel c j := by
    intro col i j
    rw [hlabel,hlabel]
    fin_cases col <;> fin_cases i <;> fin_cases j <;>
      norm_num [triangleWord,optimalLabel] <;> grind
  exact Q.canonical_lower_bound hpattern

end FiniteProgram
end HadwigerRamsey4Col
