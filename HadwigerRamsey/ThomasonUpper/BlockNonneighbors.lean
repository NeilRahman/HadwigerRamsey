import HadwigerRamsey.ThomasonUpper.NonneighborSampling
import HadwigerRamsey.ThomasonUpper.CompleteEquipartition

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

noncomputable def blockVertices {I V : Type*} [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (b : I) : Finset V := univ.image (fun y => e (b,y))

noncomputable def transversalVertices {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (x : I → Fin s) : Finset V := univ.image (fun b => e (b,x b))

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- Common nonneighbors, excluding every vertex of the part itself. -/
def commonNonneighbors {V : Type*} (G : SimpleGraph V) (W : Finset V) : Set V :=
  {v | ∀ u ∈ W, Gᶜ.Adj v u}

noncomputable def nonneighborIndices {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (e : I × Fin s ≃ V) (x : I → Fin s) (b : I) : Finset (Fin s) :=
  univ.filter (fun y => e (b,y) ∈ commonNonneighbors G (transversalVertices e x))

theorem blockVertices_card {I V : Type*} [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (b : I) : (blockVertices e b).card = s := by
  rw [blockVertices,card_image_of_injective,card_univ,Fintype.card_fin]
  intro x y h
  exact congrArg Prod.snd (e.injective h)

theorem nonneighborIndices_exclude {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (e : I × Fin s ≃ V) (x : I → Fin s) (b : I) :
    x b ∉ nonneighborIndices G e x b := by
  intro h
  have hm := (mem_filter.mp h).2
  have hv : e (b,x b) ∈ transversalVertices e x := mem_image.mpr ⟨b,mem_univ _,rfl⟩
  exact (Gᶜ).loopless.irrefl _ (hm _ hv)

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The index count in a block is precisely the vertex count used in
the already proved block-expectation estimate. -/
theorem nonneighborIndices_card_eq {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] {s : ℕ} (G : SimpleGraph V) (e : I × Fin s ≃ V)
    (p : I → Equiv.Perm (Fin s)) (t : Fin s) (b : I) :
    (nonneighborIndices G e (fun i => p i t) b).card =
      blockNonneighborCount G e t (blockVertices e b) p := by
  have he : (nonneighborIndices G e (fun i => p i t) b).image (fun y => e (b,y)) =
      (blockVertices e b).filter (fun v => p ∈ blockNonneighborEvent G e t v) := by
    ext v
    simp only [nonneighborIndices,blockVertices,filter_image,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y,?_,rfl⟩
      change blockPart e p t ⊆ univ.filter (Gᶜ.Adj (e (b,y)))
      intro w hw
      exact mem_filter.mpr ⟨mem_univ _,hy w hw⟩
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y,?_,rfl⟩
      intro w hw
      exact (mem_filter.mp (hy hw)).2
  have hinj : Function.Injective (fun y : Fin s => e (b,y)) :=
    fun x y h => congrArg Prod.snd (e.injective h)
  have hh := congrArg Finset.card he
  rw [card_image_of_injective _ hinj] at hh
  exact hh

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- If two distinct random parts have no edge between them, every
second-part index lies in the first part's common-nonneighbor indices. -/
theorem no_edge_second_part_indices {I V : Type*} [Fintype I] [DecidableEq V]
    {s : ℕ} (G : SimpleGraph V) (e : I × Fin s ≃ V)
    (p : I → Equiv.Perm (Fin s)) (t u : Fin s) (htu : t ≠ u)
    (hno : ¬PartsJoined G (blockPart e p t) (blockPart e p u)) :
    ∀ b, p b u ∈ nonneighborIndices G e (fun i => p i t) b := by
  intro b
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro v hv
  have hw : e (b,p b u) ∈ blockPart e p u := (mem_blockPart_iff e p u _).mpr ⟨b,rfl⟩
  have hne : e (b,p b u) ≠ v := by
    intro h
    exact Finset.disjoint_left.mp (blockPart_disjoint e p htu) hv (h ▸ hw)
  rw [SimpleGraph.compl_adj]
  exact ⟨hne,fun h => hno ⟨v,hv,_,hw,G.adj_symm h⟩⟩

end HadwigerRamsey.ThomasonUpper
