import HadwigerRamsey.ThomasonUpper.Density

open scoped Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Passing from an induced graph back to the original vertex type preserves
the number of ordered edges between the corresponding vertex subsets. -/
theorem card_induced_interedges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) (S T : Finset W) :
    ((G.induce W).interedges S T).card =
      (G.interedges (S.image Subtype.val) (T.image Subtype.val)).card := by
  classical
  apply card_bij (fun e _ => (e.1.val, e.2.val))
  · intro e he
    obtain ⟨hx, hy, hxy⟩ := (G.induce W).mem_interedges_iff.mp he
    exact G.mem_interedges_iff.mpr
      ⟨mem_image_of_mem Subtype.val hx, mem_image_of_mem Subtype.val hy, hxy⟩
  · intro e _ f _ hef
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hef))
      (Subtype.ext (congrArg Prod.snd hef))
  · intro e he
    obtain ⟨hx, hy, hxy⟩ := G.mem_interedges_iff.mp he
    obtain ⟨x, hxS, hx⟩ := mem_image.mp hx
    obtain ⟨y, hyT, hy⟩ := mem_image.mp hy
    refine ⟨(x,y), (G.induce W).mem_interedges_iff.mpr ⟨hxS, hyT, ?_⟩, ?_⟩
    · change G.Adj x.val y.val
      simpa only [hx, hy] using hxy
    · exact Prod.ext hx hy

theorem edgeDensity_induced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) (S T : Finset W) :
    (G.induce W).edgeDensity S T = G.edgeDensity (S.image Subtype.val) (T.image Subtype.val) := by
  classical
  simp only [SimpleGraph.edgeDensity_def, card_induced_interedges,
    card_image_of_injective _ Subtype.val_injective]

theorem internalDensity_induced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) (S : Finset W) :
    internalDensity (G.induce W) S = internalDensity G (S.image Subtype.val) := by
  classical
  have hh := card_induced_interedges G W S S
  have hleft := card_internal_interedges (G.induce W) S
  have hright := card_internal_interedges G (S.image Subtype.val)
  have hh2 := hleft.symm.trans (hh.trans hright)
  have hc := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hh2
  simp only [internalDensity, card_image_of_injective _ Subtype.val_injective]
  exact congrArg (fun c : ℕ => (c : ℝ)/(S.card.choose 2 : ℝ)) hc

end HadwigerRamsey.ThomasonUpper
