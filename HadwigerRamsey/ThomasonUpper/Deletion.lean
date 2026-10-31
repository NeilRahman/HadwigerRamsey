import Mathlib

open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Removing the first endpoint of each defective ordered pair costs no more
than the number of defects. This is the finite deletion step in the
complete-equipartition lemma, before vertices are redistributed. -/
theorem discard_defective_pairs {I : Type*} [DecidableEq I]
    (S : Finset I) (R : I → I → Prop) [DecidableRel R] :
    ∃ T : Finset I, T ⊆ S ∧
      S.card ≤ T.card + ((S ×ˢ S).filter fun e => e.1 ≠ e.2 ∧ ¬R e.1 e.2).card ∧
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → R a b := by
  let Z := (S ×ˢ S).filter fun e => e.1 ≠ e.2 ∧ ¬R e.1 e.2
  let D := Z.image Prod.fst
  refine ⟨S \ D, sdiff_subset, ?_, ?_⟩
  · exact (card_le_card_sdiff_add_card (s := S) (t := D)).trans
      (Nat.add_le_add_left (card_image_le : D.card ≤ Z.card) _)
  · intro a ha b hb hab
    by_contra hnot
    have haz : (a, b) ∈ Z := mem_filter.mpr
      ⟨mem_product.mpr ⟨(mem_sdiff.mp ha).1, (mem_sdiff.mp hb).1⟩, hab, hnot⟩
    exact (mem_sdiff.mp ha).2 (mem_image.mpr ⟨(a, b), haz, rfl⟩)

end HadwigerRamsey.ThomasonUpper
