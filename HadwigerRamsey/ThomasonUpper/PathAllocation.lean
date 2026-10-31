import HadwigerRamsey.ThomasonUpper.Menger
import HadwigerRamsey.ThomasonUpper.Selection

open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- A vertex set smaller than an internally disjoint path family cannot
meet every path interior. This is the greedy avoidance step in the appendix. -/
theorem exists_path_avoiding {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (P : Finset (G.Path u v)) (U : Finset (Fin n))
    (hd : (P : Set (G.Path u v)).PairwiseDisjoint pathInterior)
    (hcard : U.card < P.card) :
    ∃ p ∈ P, Disjoint (pathInterior p) U := by
  classical
  by_contra! h
  have hmeet : ∀ p : P, ∃ x : U, x.val ∈ pathInterior p.val := by
    intro p
    obtain ⟨x, hx, hxU⟩ := Finset.not_disjoint_iff.mp (h p.val p.property)
    exact ⟨⟨x, hxU⟩, hx⟩
  choose f hf using hmeet
  have hinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    by_contra hpne
    exact Finset.disjoint_left.mp (hd p.property q.property hpne)
      (hf p) (by simpa [hpq] using hf q)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hc
  omega

/-- Allocate one short candidate path for every requested pair of distinct
endpoints, with all interiors disjoint. The reservoir and candidate families
are hypotheses here; their probabilistic existence is a separate lemma. -/
theorem allocate_path_interiors {n : ℕ} {G : SimpleGraph (Fin n)}
    {I : Type*} [Fintype I] [DecidableEq I]
    (u v : I → Fin n) (huv : ∀ i, u i ≠ v i)
    (C : Finset (Fin n)) (H : ℕ)
    (P : ∀ i, Finset (G.Path (u i) (v i)))
    (hd : ∀ i, (P i : Set (G.Path (u i) (v i))).PairwiseDisjoint pathInterior)
    (hC : ∀ i, ∀ p ∈ P i, pathInterior p ⊆ C)
    (hlen : ∀ i, ∀ p ∈ P i, p.val.length ≤ H)
    (hcard : ∀ i, Fintype.card I * (H - 1) < (P i).card) :
    ∃ p : ∀ i, G.Path (u i) (v i),
      (∀ i, p i ∈ P i) ∧
      (∀ i, pathInterior (p i) ⊆ C) ∧
      (∀ i j, i ≠ j → Disjoint (pathInterior (p i)) (pathInterior (p j))) := by
  classical
  obtain ⟨M, hM, hdisj⟩ := disjoint_reservoir_selection C (H - 1)
    (fun i N => ∃ p ∈ P i, N = pathInterior p) (by
      intro i U _ hU
      obtain ⟨p, hp, hpU⟩ := exists_path_avoiding (P i) U (hd i) (hU.trans_lt (hcard i))
      refine ⟨pathInterior p, ?_, ?_, p, hp, rfl⟩
      · intro x hx
        exact mem_sdiff.mpr ⟨hC i p hp hx, fun hxU => Finset.disjoint_left.mp hpU hx hxU⟩
      · have hc := pathInterior_card (huv i) p
        have hl := hlen i p hp
        omega)
  choose p hp heq using fun i => (hM i).2.2
  refine ⟨p, hp, ?_, ?_⟩
  · intro i
    rw [← heq i]
    exact (hM i).1
  · intro i j hij
    rw [← heq i, ← heq j]
    exact hdisj i j hij

end HadwigerRamsey.ThomasonUpper
