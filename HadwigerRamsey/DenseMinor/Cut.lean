import HadwigerRamsey.BipMinor
import HadwigerRamsey.Existence.Blocks

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.DenseMinor

/-- Keep just the edges crossing the two vertex classes. -/
def cutGraph {V : Type*} (G : SimpleGraph V) (c : V → Fin 2) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ c u ≠ c v
  symm := ⟨fun _ _ h => ⟨G.adj_symm h.1,Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩
lemma cutGraph_le {V : Type*} (G : SimpleGraph V) (c : V → Fin 2) : cutGraph G c ≤ G := fun _ _ h => h.1
lemma cutGraph_proper {V : Type*} (G : SimpleGraph V) (c : V → Fin 2) :
    ∀ u v, (cutGraph G c).Adj u v → c u ≠ c v := fun _ _ h => h.2

/-- The cross edges of the cut graph are exactly the original cross edges. -/
lemma cut_cross_edges {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2) :
    (cutGraph G c).interedges (classVertices c 0) (classVertices c 1) =
      G.interedges (classVertices c 0) (classVertices c 1) := by
  ext e
  simp only [SimpleGraph.mem_interedges_iff]
  constructor
  · rintro ⟨hu,hv,h⟩; exact ⟨hu,hv,h.1⟩
  · rintro ⟨hu,hv,h⟩
    refine ⟨hu,hv,h,?_⟩
    rw [(mem_filter.mp hu).2,(mem_filter.mp hv).2]
    decide

lemma cut_card {n a : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (hsize : ∀ i, (classVertices c i).card = a) :
    (cutGraph G c).edgeFinset.card = (G.interedges (classVertices c 0) (classVertices c 1)).card := by
  let C := cutGraph G c
  have hh := sum_card_block_interedges C c
  letI : Std.Symm C.Adj := C.symm
  have hc := Rel.card_interedges_comm (r := C.Adj) (classVertices c 0) (classVertices c 1)
  change (C.interedges (classVertices c 0) (classVertices c 1)).card = (C.interedges (classVertices c 1) (classVertices c 0)).card at hc
  simp only [Fin.sum_univ_two,BipMinor.diagonal_interedges_empty C c (cutGraph_proper G c),card_empty,zero_add,add_zero] at hh
  have he : C.edgeFinset.card = (C.interedges (classVertices c 0) (classVertices c 1)).card := by omega
  exact he.trans (congrArg card (cut_cross_edges G c))

lemma half_card {a : ℕ} (ha : 0 < a) (i : Fin 2) :
    (classVertices (Existence.halfClass (m := a)) i).card = a := by
  have hh := Existence.half_mass ha i
  change ((classVertices (Existence.halfClass (m := a)) i).card : ℝ)/(2*a : ℕ) = 1/2 at hh
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  push_cast at hh
  have he : ((classVertices (Existence.halfClass (m := a)) i).card : ℝ) = a := by
    have hh' := (div_eq_iff (show (2*(a : ℝ)) ≠ 0 by positivity)).mp hh
    linarith only [hh']
  exact_mod_cast he

/-- A bound using all missing ordered pairs, including the diagonal.
The harmless diagonal contribution is absorbed in the eventual cutoff. -/
lemma cross_missing_bound {n a : ℕ} (H : SimpleGraph (Fin n))
    (f : Fin (2*a) → Fin n) (hf : Function.Injective f) (ha : 0 < a) :
    ((cutGraph (H.comap f) Existence.halfClass).edgeFinset.card : ℝ) +
      (n : ℝ)^2 - 2*(H.edgeFinset.card : ℝ) ≥ (a : ℝ)^2 := by
  let c := Existence.halfClass (m := a)
  let A := classVertices c 0
  let B := classVertices c 1
  have hpair := Rel.card_interedges_add_card_interedges_compl
    (r := (H.comap f).Adj) A B
  have hnon : (Rel.interedges (fun u v => ¬(H.comap f).Adj u v) A B).card ≤
      (Rel.interedges (fun u v => ¬H.Adj u v) univ univ).card := by
    apply card_le_card_of_injOn (f := fun e => (f e.1,f e.2))
    · intro e he
      obtain ⟨hu,hv,h⟩ := Rel.mem_interedges_iff.mp he
      exact Rel.mem_interedges_iff.mpr ⟨mem_univ _,mem_univ _,h⟩
    · intro e he d hd h
      exact Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  have hall := Rel.card_interedges_add_card_interedges_compl (r := H.Adj) (univ : Finset (Fin n)) univ
  have hyes : (Rel.interedges H.Adj univ univ).card = 2*H.edgeFinset.card := by
    simpa [SimpleGraph.interedges_def,Rel.interedges] using H.two_mul_card_edgeFinset.symm
  rw [hyes,card_univ,Fintype.card_fin] at hall
  have hcut := cut_card (H.comap f) c (half_card ha)
  change (cutGraph (H.comap f) c).edgeFinset.card = (Rel.interedges (H.comap f).Adj A B).card at hcut
  have hA : A.card = a := half_card ha 0
  have hB : B.card = a := half_card ha 1
  rw [hA,hB,← hcut] at hpair
  have hpairR : ((cutGraph (H.comap f) c).edgeFinset.card : ℝ) +
      (Rel.interedges (fun u v => ¬(H.comap f).Adj u v) A B).card = (a : ℝ)^2 := by rw [pow_two]; exact_mod_cast hpair
  have hallR : 2*(H.edgeFinset.card : ℝ) + (Rel.interedges (fun u v => ¬H.Adj u v) univ univ).card = (n : ℝ)^2 := by rw [pow_two]; exact_mod_cast hall
  have hnonR : ((Rel.interedges (fun u v => ¬(H.comap f).Adj u v) A B).card : ℝ) ≤
      (Rel.interedges (fun u v => ¬H.Adj u v) univ univ).card := by exact_mod_cast hnon
  linarith only [hpairR,hallR,hnonR]
end HadwigerRamsey.DenseMinor

namespace HadwigerRamsey.DenseMinor
open scoped Classical
open Finset
open HadwigerRamsey.ThomasonUpper
lemma cut_bipartite {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2) :
    (cutGraph G c).IsBipartiteWith (classVertices c 0 : Set (Fin n)) (classVertices c 1 : Set (Fin n)) := by
  refine ⟨?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro v hv hw
    have hv' := (mem_filter.mp hv).2
    have hw' := (mem_filter.mp hw).2
    exact (by decide : (0 : Fin 2) ≠ 1) (hv'.symm.trans hw')
  · intro u v huv
    have hcases : ∀ i j : Fin 2, i ≠ j → (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
      intro i j; fin_cases i <;> fin_cases j <;> simp
    rcases hcases (c u) (c v) huv.2 with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact Or.inl ⟨mem_filter.mpr ⟨mem_univ _,hu⟩,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
    · exact Or.inr ⟨mem_filter.mpr ⟨mem_univ _,hu⟩,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
lemma classes_cover {n : ℕ} (c : Fin n → Fin 2) : classVertices c 0 ∪ classVertices c 1 = univ := by
  ext v
  have hh : ∀ i : Fin 2, i=0 ∨ i=1 := by intro i; fin_cases i <;> simp
  simp only [mem_union,classVertices,mem_filter,mem_univ,true_and,iff_true]
  exact hh (c v)
end HadwigerRamsey.DenseMinor
