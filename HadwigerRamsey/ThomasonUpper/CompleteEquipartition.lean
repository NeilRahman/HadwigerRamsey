import HadwigerRamsey.ThomasonUpper.BalancedExtension
import HadwigerRamsey.ThomasonUpper.Deletion

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Two parts have at least one edge between them. -/
def PartsJoined {V : Type*} (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ∃ u ∈ S, ∃ v ∈ T, G.Adj u v

/-- An indexed complete equipartition, with nonempty parts. Its part
sizes differ by at most one, as in the manuscript. -/
structure IsCompleteEquipartition {V : Type*} (G : SimpleGraph V) {m : ℕ}
    (W : Fin m → Finset V) : Prop where
  nonempty : ∀ i, (W i).Nonempty
  disjoint : Pairwise (fun i j => Disjoint (W i) (W j))
  cover : ∀ v, ∃ i, v ∈ W i
  balanced : ∀ i j, (W i).card ≤ (W j).card+1
  complete : ∀ i j, i ≠ j → PartsJoined G (W i) (W j)

/-- The part sizes sum to the full vertex count. -/
theorem IsCompleteEquipartition.sum_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {m : ℕ} {W : Fin m → Finset V}
    (hW : IsCompleteEquipartition G W) : ∑ i, (W i).card = Fintype.card V := by
  classical
  have hcover : univ.biUnion W = univ := by
    ext v
    simp only [mem_biUnion,mem_univ,true_and,iff_true]
    exact hW.cover v
  have hh := card_biUnion (s := univ) (t := W)
    (fun i _ j _ hij => hW.disjoint hij)
  rw [hcover,card_univ] at hh
  exact hh.symm

/-- Mathlib's equitable-family bound gives the precise floor-average
part sizes needed when A.1 is used in the asymptotic corollary. -/
theorem IsCompleteEquipartition.card_part_bounds {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {m : ℕ} {W : Fin m → Finset V}
    (hW : IsCompleteEquipartition G W) (i : Fin m) :
    Fintype.card V/m ≤ (W i).card ∧ (W i).card ≤ Fintype.card V/m+1 := by
  have heq : Set.EquitableOn (univ : Finset (Fin m)) (fun j => (W j).card) :=
    fun _ _ _ _ => hW.balanced _ _
  have hh := (equitableOn_iff_le_le_add_one.mp heq) i (mem_univ _)
  simpa only [hW.sum_card,card_univ,Fintype.card_fin] using hh

/-- A nonempty complete subfamily of disjoint equal-size sets extends
to a complete equipartition of all vertices. -/
theorem complete_equipartition_of_equal_cores {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {s L : ℕ} (W : Fin s → Finset V) (hL : 0 < L)
    (hcard : ∀ i, (W i).card = L)
    (hdisj : Pairwise (fun i j => Disjoint (W i) (W j)))
    (T : Finset (Fin s)) (hT : T.Nonempty)
    (hcomplete : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → PartsJoined G (W i) (W j)) :
    ∃ U : Fin T.card → Finset V, IsCompleteEquipartition G U := by
  classical
  letI : Nonempty T := ⟨⟨hT.choose,hT.choose_spec⟩⟩
  obtain ⟨U,hsub,hUdisj,hcover,hbal⟩ := extend_equal_cores
    (fun i : T => W i) (fun i j hij => hdisj (fun h => hij (Subtype.ext h)))
    (fun i => hcard i)
  let e : Fin T.card ≃ T := T.equivFin.symm
  refine ⟨fun i => U (e i),?_,?_,?_,?_,?_⟩
  · intro i
    exact (card_pos.mp (by rw [hcard]; exact hL)).mono (hsub (e i))
  · intro i j hij
    exact hUdisj (fun h => hij (e.injective h))
  · intro v
    obtain ⟨i,hi⟩ := hcover v
    exact ⟨e.symm i,by simpa using hi⟩
  · intro i j
    exact hbal _ _
  · intro i j hij
    obtain ⟨u,hu,v,hv,huv⟩ := hcomplete _ (e i).property _ (e j).property
      (fun h => hij (e.injective (Subtype.ext h)))
    exact ⟨u,hsub _ hu,v,hsub _ hv,huv⟩

/-- Delete at most one endpoint per defective ordered pair, then
redistribute the removed vertices. This is the final deterministic step
of the finite complete-equipartition lemma. -/
theorem complete_equipartition_after_defects {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {s L : ℕ} (W : Fin s → Finset V) (hL : 0 < L)
    (hcard : ∀ i, (W i).card = L)
    (hdisj : Pairwise (fun i j => Disjoint (W i) (W j)))
    (A : Finset (Fin s)) {b : ℝ}
    (hdef : (((A ×ˢ A).filter (fun e => e.1 ≠ e.2 ∧ ¬PartsJoined G (W e.1) (W e.2))).card : ℝ) ≤ b)
    (hpos : b < (A.card : ℝ)) :
    ∃ m : ℕ, ∃ U : Fin m → Finset V,
      0 < m ∧ m ≤ s ∧ (A.card : ℝ)-b ≤ m ∧ IsCompleteEquipartition G U := by
  classical
  obtain ⟨T,hTA,hTcard,hTcomplete⟩ := discard_defective_pairs A
    (fun i j => PartsJoined G (W i) (W j))
  have hcardR : (A.card : ℝ) ≤ T.card+
      (((A ×ˢ A).filter (fun e => e.1 ≠ e.2 ∧ ¬PartsJoined G (W e.1) (W e.2))).card : ℝ) := by
    exact_mod_cast hTcard
  have hTpos : 0 < T.card := by
    have hR : (0 : ℝ) < T.card := by linarith
    exact_mod_cast hR
  obtain ⟨U,hU⟩ := complete_equipartition_of_equal_cores G W hL hcard hdisj T
    (card_pos.mp hTpos) hTcomplete
  refine ⟨T.card,U,hTpos,?_,by linarith,hU⟩
  exact (card_le_card hTA).trans (by simpa using card_le_univ A)

end HadwigerRamsey.ThomasonUpper
