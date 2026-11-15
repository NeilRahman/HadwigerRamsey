import HadwigerRamsey.ThomasonUpper.Connectivity
import Lax17Proofs.Source.Menger
import HadwigerRamsey.ThomasonUpper.ShortPaths

open Finset
open scoped Classical
open Lax17Proofs.SimpleGraph

namespace HadwigerRamsey.ThomasonUpper

/-- Removing the end edges of a path between nonadjacent vertices leaves
a path between their neighborhoods, entirely in its original interior. -/
theorem path_middle {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : u ≠ v) (hnon : ¬ G.Adj u v) (p : G.Path u v) :
    ∃ Q : GraphPath G, G.Adj u Q.source ∧ G.Adj Q.target v ∧
      Q.vertexSet ⊆ pathInterior p := by
  classical
  let P : GraphPath G := ⟨u, v, p.val, p.property⟩
  let A := P.reverse.dropLast.reverse
  have hstart : G.Adj u A.source :=
    (P.reverse.penultimate_adj_target huv.symm).symm
  have hAv : A.source ≠ A.target := by
    change A.source ≠ v
    intro heq
    exact hnon (heq ▸ hstart)
  have hsub : A.vertexSet ⊆ P.vertexSet := by
    simpa [A] using P.reverse.dropLast_vertexSet_subset
  have hnotu : u ∉ A.vertexSet := by
    simpa [A, P] using P.reverse.target_not_mem_dropLast_vertexSet huv.symm
  refine ⟨A.dropLast, hstart, A.penultimate_adj_target hAv, ?_⟩
  intro x hx
  apply mem_sdiff.mpr
  refine ⟨hsub (A.dropLast_vertexSet_subset hx), ?_⟩
  intro hxe
  rcases mem_insert.mp hxe with rfl | hxe
  · exact hnotu (A.dropLast_vertexSet_subset hx)
  · rw [mem_singleton] at hxe
    subst x
    exact A.target_not_mem_dropLast_vertexSet hAv hx

/-- The public Menger theorem applied to the project's cut-based definition
of vertex connectivity. Both terminal sets may intersect. -/
theorem disjoint_paths_between_large_sets {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hconn : VertexConnectedAtLeast G k) (S T : Finset (Fin n))
    (hS : k ≤ S.card) (hT : k ≤ T.card) :
    HasDisjointSTPaths G S T k := by
  classical
  rcases Menger.finite_vertex_menger_sharp G S T k with h | ⟨Z, hZ, hsep⟩
  · exact h
  · obtain ⟨u, huS, huZ⟩ := exists_mem_notMem_of_card_lt_card (hZ.trans_le hS)
    obtain ⟨v, hvT, hvZ⟩ := exists_mem_notMem_of_card_lt_card (hZ.trans_le hT)
    obtain ⟨p⟩ := hconn.2 Z hZ ⟨u, huZ⟩ ⟨v, hvZ⟩
    let f : G.induce ((Z : Set (Fin n))ᶜ) →g G :=
      ⟨Subtype.val, fun h => h⟩
    let P := GraphPath.ofWalk (p.map f)
    obtain ⟨x, hxP, hxZ⟩ := hsep P (Or.inl ⟨huS, hvT⟩)
    have hx : x ∈ (p.map f).support := List.mem_toFinset.mp
      (GraphPath.ofWalk_vertexSet_subset (p.map f) hxP)
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨y, _, hy⟩ := List.mem_map.mp hx
    exfalso
    apply y.property
    change f y ∈ Z
    rw [hy]
    exact hxZ

/-- The neighborhood form of Menger for two nonadjacent vertices. The
packing lives outside the two endpoints, so its paths are fully disjoint. -/
theorem neighbor_paths_of_nonadjacent {n k : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (hnon : ¬G.Adj u v)
    (hconn : VertexConnectedAtLeast G k) :
    let U : Finset (Fin n) := univ \ {u, v}
    HasDisjointSTPaths (G.induce (U : Set (Fin n)))
      (univ.filter fun x => G.Adj u x.val)
      (univ.filter fun x => G.Adj x.val v) k := by
  classical
  dsimp only
  let U : Finset (Fin n) := univ \ {u, v}
  let H := G.induce (U : Set (Fin n))
  let S : Finset U := univ.filter fun x => G.Adj u x.val
  let T : Finset U := univ.filter fun x => G.Adj x.val v
  change HasDisjointSTPaths H S T k
  rcases Menger.finite_vertex_menger_sharp H S T k with h | ⟨Z, hZ, hsep⟩
  · exact h
  · let Z₀ := Z.image Subtype.val
    have hZ₀ : Z₀.card < k := card_image_le.trans_lt hZ
    have he : ∀ x ∈ Z₀, x ≠ u ∧ x ≠ v := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_image.mp hx
      simpa [U] using y.property
    have huZ : u ∉ Z₀ := fun h => (he u h).1 rfl
    have hvZ : v ∉ Z₀ := fun h => (he v h).2 rfl
    obtain ⟨q, hq⟩ := (hconn.2 Z₀ hZ₀).exists_isPath ⟨u, huZ⟩ ⟨v, hvZ⟩
    let f : G.induce ((Z₀ : Set (Fin n))ᶜ) →g G :=
      ⟨Subtype.val, fun h => h⟩
    let p : G.Path u v := ⟨q.map f,
      (SimpleGraph.Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hq⟩
    obtain ⟨Q, huQ, hQv, hQ⟩ := path_middle huv hnon p
    have hQU : Q.vertexSet ⊆ U := by
      intro x hx
      exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp (hQ hx)).2⟩
    let R := Q.induce U hQU
    have hR : R.Connects S T := Or.inl
      ⟨mem_filter.mpr ⟨mem_univ _, huQ⟩, mem_filter.mpr ⟨mem_univ _, hQv⟩⟩
    obtain ⟨x, hxR, hxZ⟩ := hsep R hR
    have hxQ : x.val ∈ Q.vertexSet := (Q.mem_induce_vertexSet U hQU x).mp hxR
    have hxP : x.val ∈ (q.map f).support :=
      List.mem_toFinset.mp (mem_sdiff.mp (hQ hxQ)).1
    rw [SimpleGraph.Walk.support_map] at hxP
    obtain ⟨y, _, hy⟩ := List.mem_map.mp hxP
    exfalso
    apply y.property
    change f y ∈ Z₀
    rw [hy]
    exact mem_image_of_mem Subtype.val hxZ

/-- Adjoin the two missing endpoint edges to an interior path. No cycle
erasure is necessary, and its interior is exactly the original vertex set. -/
theorem extend_inner_path {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : u ≠ v)
    (Q : GraphPath (G.induce ((univ \ {u, v} : Finset (Fin n)) : Set (Fin n))))
    (hu : G.Adj u Q.source.val) (hv : G.Adj Q.target.val v) :
    ∃ p : G.Path u v, pathInterior p = Q.vertexSet.image Subtype.val := by
  classical
  let U : Finset (Fin n) := univ \ {u, v}
  let f : G.induce (U : Set (Fin n)) →g G := ⟨Subtype.val, fun h => h⟩
  let w := Q.walk.map f
  have hw : w.IsPath :=
    (SimpleGraph.Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr Q.isPath
  have havoid : ∀ x ∈ w.support, x ≠ u ∧ x ≠ v := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    change y.val ≠ u ∧ y.val ≠ v
    simpa [U] using y.property
  have hnu : u ∉ w.support := fun h => (havoid u h).1 rfl
  have hnv : v ∉ w.support := fun h => (havoid v h).2 rfl
  have hnu' : u ∉ (w.concat hv).support := by
    rw [SimpleGraph.Walk.support_concat]
    simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro hnu huv
  let p : G.Path u v := ⟨SimpleGraph.Walk.cons hu (w.concat hv),
    (hw.concat hnv hv).cons hnu'⟩
  refine ⟨p, ?_⟩
  have hmem : ∀ x, x ∈ w.support.toFinset ↔ x ∈ Q.vertexSet.image Subtype.val := by
    intro x
    change x ∈ (Q.walk.map f).support.toFinset ↔ x ∈ Q.vertexSet.image Subtype.val
    rw [SimpleGraph.Walk.support_map]
    simp only [List.mem_toFinset, List.mem_map, mem_image, GraphPath.vertexSet]
    rfl
  ext x
  simp only [pathInterior, mem_sdiff]
  change (x ∈ (SimpleGraph.Walk.cons hu (w.concat hv)).support.toFinset ∧
    x ∉ ({u, v} : Finset (Fin n))) ↔ _
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat]
  simp only [
    List.mem_toFinset, List.mem_cons, List.mem_append,
    mem_insert, mem_singleton]
  have hx := hmem x
  simp only [List.mem_toFinset] at hx
  have ha := havoid x
  tauto

/-- Convert a neighborhood packing into internally disjoint endpoint paths. -/
theorem internally_disjoint_paths_of_neighbor_packing {n k : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v)
    (hpacking : HasDisjointSTPaths
      (G.induce ((univ \ {u, v} : Finset (Fin n)) : Set (Fin n)))
      (univ.filter fun x => G.Adj u x.val)
      (univ.filter fun x => G.Adj x.val v) k) :
    ∃ P : Finset (G.Path u v), k ≤ P.card ∧
      (P : Set (G.Path u v)).PairwiseDisjoint pathInterior ∧
      ∀ p ∈ P, (pathInterior p).Nonempty := by
  classical
  obtain ⟨A, hA⟩ := hpacking
  let Q := fun i : A.Index => (A.path i).orient (A.connects i)
  have hQS : ∀ i, G.Adj u (Q i).source.val := fun i =>
    (mem_filter.mp ((A.path i).orient_source_mem (A.connects i))).2
  have hQT : ∀ i, G.Adj (Q i).target.val v := fun i =>
    (mem_filter.mp ((A.path i).orient_target_mem (A.connects i))).2
  choose p hp using fun i => extend_inner_path huv (Q i) (hQS i) (hQT i)
  have hdisj : Pairwise fun i j => Disjoint (pathInterior (p i)) (pathInterior (p j)) := by
    intro i j hij
    rw [hp i, hp j, Finset.disjoint_image Subtype.val_injective]
    simpa [Q] using A.node_disjoint hij
  have hnonempty : ∀ i, (pathInterior (p i)).Nonempty := by
    intro i
    rw [hp i]
    exact ⟨(Q i).source.val, mem_image.mpr ⟨(Q i).source, (Q i).source_mem_vertexSet, rfl⟩⟩
  have hinj : Function.Injective p := by
    intro i j hij
    by_contra hne
    obtain ⟨x, hx⟩ := hnonempty i
    exact Finset.disjoint_left.mp (hdisj hne) hx (hij ▸ hx)
  refine ⟨univ.image p, ?_, ?_, ?_⟩
  · simpa [card_image_of_injective _ hinj, PathPacking.card] using hA
  · intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := mem_image.mp hb
    exact hdisj (fun hij => hab (congrArg p hij))
  · intro a ha
    obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    exact hnonempty i

/-- The usual internally disjoint version of Menger for nonadjacent vertices. -/
theorem internally_disjoint_paths_of_nonadjacent {n k : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (hnon : ¬G.Adj u v)
    (hconn : VertexConnectedAtLeast G k) :
    ∃ P : Finset (G.Path u v), k ≤ P.card ∧
      (P : Set (G.Path u v)).PairwiseDisjoint pathInterior := by
  obtain ⟨P, hc, hd, _⟩ := internally_disjoint_paths_of_neighbor_packing huv
    (neighbor_paths_of_nonadjacent huv hnon hconn)
  exact ⟨P, hc, hd⟩

/-- For arbitrary distinct endpoints one can pack at least k-1 paths
between their neighborhoods outside the endpoints. -/
theorem neighbor_paths_pred {n k : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (hconn : VertexConnectedAtLeast G k) :
    HasDisjointSTPaths
      (G.induce ((univ \ {u, v} : Finset (Fin n)) : Set (Fin n)))
      (univ.filter fun x => G.Adj u x.val)
      (univ.filter fun x => G.Adj x.val v) (k - 1) := by
  classical
  let U : Finset (Fin n) := univ \ {u, v}
  let H := G.induce (U : Set (Fin n))
  let S : Finset U := univ.filter fun x => G.Adj u x.val
  let T : Finset U := univ.filter fun x => G.Adj x.val v
  change HasDisjointSTPaths H S T (k - 1)
  rcases Menger.finite_vertex_menger_sharp H S T (k - 1) with h | ⟨Z, hZ, hsep⟩
  · exact h
  · let Z₀ := Z.image Subtype.val
    have hZ₀ : Z₀.card < k - 1 := card_image_le.trans_lt hZ
    have he : ∀ x ∈ Z₀, x ≠ u ∧ x ≠ v := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_image.mp hx
      simpa [U] using y.property
    have huZ : u ∉ Z₀ := fun h => (he u h).1 rfl
    have hvZ : v ∉ Z₀ := fun h => (he v h).2 rfl
    have hcard : (insert v Z₀).card < (G.neighborFinset u).card := by
      have hd := hconn.le_degree u
      have hi := card_insert_le v Z₀
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨w, hw, hwout⟩ := exists_mem_notMem_of_card_lt_card hcard
    have huw : G.Adj u w := by simpa using hw
    have hwu : w ≠ u := (G.ne_of_adj huw).symm
    have hwv : w ≠ v := fun h => hwout (by simp [h])
    have hwZ : w ∉ Z₀ := fun h => hwout (mem_insert_of_mem h)
    have hi : (insert u Z₀).card < k := by rw [card_insert_of_notMem huZ]; omega
    obtain ⟨q⟩ := hconn.2 (insert u Z₀) hi
      ⟨w, by simpa [hwu] using hwZ⟩ ⟨v, by simpa [huv.symm] using hvZ⟩
    let f : G.induce (((insert u Z₀ : Finset (Fin n)) : Set (Fin n))ᶜ) →g G :=
      ⟨Subtype.val, fun h => h⟩
    let P := GraphPath.ofWalk (q.map f)
    let Q := P.dropLast
    have havoid : ∀ x ∈ Q.vertexSet, x ≠ u ∧ x ≠ v ∧ x ∉ Z₀ := by
      intro x hx
      have hxq : x ∈ (q.map f).support := List.mem_toFinset.mp
        (GraphPath.ofWalk_vertexSet_subset (q.map f) (P.dropLast_vertexSet_subset hx))
      rw [SimpleGraph.Walk.support_map] at hxq
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hxq
      have hout : x ∉ insert u Z₀ := hy ▸ y.property
      refine ⟨fun h => hout (by simp [h]), ?_, fun h => hout (mem_insert_of_mem h)⟩
      intro h
      have hvQ : v ∈ Q.vertexSet := h ▸ hx
      exact P.target_not_mem_dropLast_vertexSet hwv hvQ
    have hQU : Q.vertexSet ⊆ U := by
      intro x hx
      simpa [U] using And.intro (havoid x hx).1 (havoid x hx).2.1
    let R := Q.induce U hQU
    have hR : R.Connects S T := Or.inl
      ⟨mem_filter.mpr ⟨mem_univ _, huw⟩,
       mem_filter.mpr ⟨mem_univ _, P.penultimate_adj_target hwv⟩⟩
    obtain ⟨x, hxR, hxZ⟩ := hsep R hR
    exact False.elim ((havoid x.val ((Q.mem_induce_vertexSet U hQU x).mp hxR)).2.2
      (mem_image_of_mem Subtype.val hxZ))

/-- The internally vertex-disjoint form of Menger, including adjacent
endpoints, derived from the public set-to-set theorem. -/
theorem internally_disjoint_paths {n k : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (hconn : VertexConnectedAtLeast G k) :
    ∃ P : Finset (G.Path u v), k ≤ P.card ∧
      (P : Set (G.Path u v)).PairwiseDisjoint pathInterior := by
  classical
  by_cases hadj : G.Adj u v
  · obtain ⟨P, hc, hd, hne⟩ := internally_disjoint_paths_of_neighbor_packing huv
      (neighbor_paths_pred huv hconn)
    let p₀ : G.Path u v := ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, by simp [huv]⟩
    have he : pathInterior p₀ = ∅ := by ext x; simp [pathInterior, p₀]
    have hnot : p₀ ∉ P := by
      intro h
      simpa [he] using hne p₀ h
    refine ⟨insert p₀ P, ?_, ?_⟩
    · rw [card_insert_of_notMem hnot]
      omega
    · intro a ha b hb hab
      rcases mem_insert.mp ha with rfl | ha
      · change Disjoint (pathInterior p₀) (pathInterior b)
        simp [he]
      · rcases mem_insert.mp hb with rfl | hb
        · change Disjoint (pathInterior a) (pathInterior p₀)
          simp [he]
        · exact hd ha hb hab
  · exact internally_disjoint_paths_of_nonadjacent huv hadj hconn

/-- The short-path step of Lemma A.4: at least k/2 internally disjoint paths have
length at most 2n/k+1. Positivity is explicit to give the quotient its
intended meaning. -/
theorem short_paths {n k : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (hk : 0 < k)
    (hconn : VertexConnectedAtLeast G k) :
    ∃ Q : Finset (G.Path u v), k ≤ 2 * Q.card ∧
      (∀ p ∈ Q, (p.val.length : ℝ) ≤ 2 * n / (k : ℝ) + 1) ∧
      (Q : Set (G.Path u v)).PairwiseDisjoint pathInterior := by
  obtain ⟨P, hc, hd⟩ := internally_disjoint_paths huv hconn
  obtain ⟨Q, _, hcard, hlen, hdisj⟩ := short_paths_of_family huv hk P hc hd
  exact ⟨Q, hcard, hlen, hdisj⟩

/-- The short-path step of Lemma A.4 with the graph's actual vertex connectivity and the
manuscript's real-valued lower bound on the number of paths. -/
theorem short_paths_vertexConnectivity {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (hk : 0 < vertexConnectivity G) :
    ∃ Q : Finset (G.Path u v), (vertexConnectivity G : ℝ) / 2 ≤ Q.card ∧
      (∀ p ∈ Q, (p.val.length : ℝ) ≤ 2 * n / (vertexConnectivity G : ℝ) + 1) ∧
      (Q : Set (G.Path u v)).PairwiseDisjoint pathInterior := by
  have hconn := (vertexConnectedAtLeast_iff (Fin.pos u) G (vertexConnectivity G)).2 le_rfl
  obtain ⟨Q, hcard, hlen, hd⟩ := short_paths huv hk hconn
  refine ⟨Q, ?_, hlen, hd⟩
  have hc : (vertexConnectivity G : ℝ) ≤ 2 * Q.card := by exact_mod_cast hcard
  linarith

end HadwigerRamsey.ThomasonUpper
