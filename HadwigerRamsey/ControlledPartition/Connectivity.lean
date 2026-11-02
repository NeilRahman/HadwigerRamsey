import HadwigerRamsey.ControlledPartition.Definitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

open Finset
open scoped Classical

namespace HadwigerRamsey.ControlledPartition

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S T D : Finset (Fin n)} {s t : ℝ}

namespace RealConnected

theorem mono (h : RealConnected G S t) (hst : s ≤ t) : RealConnected G S s := by
  refine ⟨hst.trans h.1, ?_⟩
  intro Z hZS hZ
  exact h.2 Z hZS (hZ.trans_le hst)

theorem delete (h : RealConnected G S t) (D : Finset (Fin n)) :
    RealConnected G (S \ D) (t - D.card) := by
  refine ⟨?_, ?_⟩
  · have hc : (S.card : ℝ) ≤ (S \ D).card + (D.card : ℝ) := by
      exact_mod_cast (card_le_card_sdiff_add_card : S.card ≤ (S \ D).card + D.card)
    linarith [h.1]
  · intro Z hZS hZ
    let W := (S ∩ D) ∪ Z
    have hWS : W ⊆ S := by
      intro v hv
      rcases mem_union.mp hv with hv | hv
      · exact (mem_inter.mp hv).1
      · exact (mem_sdiff.mp (hZS hv)).1
    have hc : (W.card : ℝ) ≤ D.card + (Z.card : ℝ) := by
      have hi : (S ∩ D).card ≤ D.card := card_le_card inter_subset_right
      exact_mod_cast (card_union_le (S ∩ D) Z).trans (Nat.add_le_add_right hi _)
    have he : S \ W = (S \ D) \ Z := by
      ext v
      simp only [W, mem_sdiff, mem_union, mem_inter]
      tauto
    have hh := h.2 W hWS (by linarith)
    convert hh using 1 <;> congr 1 <;> ext v <;> simp only [W, mem_coe, mem_sdiff, mem_union, mem_inter] <;> tauto

/-- A failed connectivity bound has a genuine separation after a small deletion. -/
theorem separator (hsize : t ≤ (S.card : ℝ)-1) (hnot : ¬RealConnected G S t) :
    ∃ Z A B : Finset (Fin n), Z ⊆ S ∧ (Z.card : ℝ) < t ∧
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = S \ Z ∧
      (∀ u ∈ A, ∀ v ∈ B, ¬G.Adj u v) := by
  classical
  have hn : ∃ Z : Finset (Fin n), Z ⊆ S ∧ (Z.card : ℝ)<t ∧
      ¬(G.induce (↑(S \ Z) : Set (Fin n))).Connected := by
    by_contra! hh
    exact hnot ⟨hsize, hh⟩
  obtain ⟨Z,hZS,hZ,hdisc⟩ := hn
  have hcard : Z.card < S.card := by
    have hh : (Z.card : ℝ) < S.card := by linarith
    exact_mod_cast hh
  obtain ⟨a,haS,haZ⟩ := exists_mem_notMem_of_card_lt_card hcard
  let a' : (↑(S \ Z) : Set (Fin n)) := ⟨a,mem_sdiff.mpr ⟨haS,haZ⟩⟩
  let H := G.induce (↑(S \ Z) : Set (Fin n))
  have hnpre : ¬ H.Preconnected := by
    intro hh
    exact hdisc {preconnected := hh, nonempty := ⟨a'⟩}
  have hb : ∃ b : (↑(S \ Z) : Set (Fin n)), ¬ H.Reachable a' b := by
    by_contra! hh
    exact hnpre (fun u v => (hh u).symm.trans (hh v))
  obtain ⟨b,hb⟩ := hb
  let A := (S \ Z).filter fun v => ∃ hv : v ∈ S \ Z, H.Reachable a' ⟨v,hv⟩
  let B := (S \ Z) \ A
  have haA : a ∈ A := by
    exact mem_filter.mpr ⟨a'.property, ⟨a'.property, SimpleGraph.Reachable.refl _⟩⟩
  have hbB : b.val ∈ B := by
    refine mem_sdiff.mpr ⟨b.property, ?_⟩
    intro hh
    obtain ⟨_,hv,hr⟩ := mem_filter.mp hh
    exact hb hr
  refine ⟨Z,A,B,hZS,hZ,⟨a,haA⟩,⟨b.val,hbB⟩,(by apply disjoint_left.mpr; intro v hv hvB; exact (mem_sdiff.mp hvB).2 hv),?_,?_⟩
  · exact union_sdiff_of_subset (filter_subset _ _)
  · intro u hu v hv huv
    obtain ⟨huS,hu',hru⟩ := mem_filter.mp hu
    obtain ⟨hvS,hvA⟩ := mem_sdiff.mp hv
    apply hvA
    refine mem_filter.mpr ⟨hvS,⟨hvS,?_⟩⟩
    exact hru.trans (show H.Adj ⟨u,hu'⟩ ⟨v,hvS⟩ from huv).reachable

theorem connected_delete (h : RealConnected G S t) (Z : Finset (Fin n))
    (hZ : (Z.card : ℝ) < t) :
    (G.induce (↑(S \ Z) : Set (Fin n))).Connected := by
  have hI : ((S ∩ Z).card : ℝ) ≤ Z.card := by
    exact_mod_cast card_le_card (show S ∩ Z ⊆ Z from inter_subset_right)
  have hh := h.2 (S ∩ Z) inter_subset_left (hI.trans_lt hZ)
  convert hh using 1 <;> congr 1 <;> ext v <;> simp only [mem_coe, mem_sdiff, mem_inter] <;> tauto

theorem add_vertex (h : RealConnected G S t) {v : Fin n} (hv : v ∉ S)
    (hdeg : t ≤ ((nbr G S v).card : ℝ)) :
    RealConnected G (insert v S) t := by
  classical
  refine ⟨?_, ?_⟩
  · have hc : S.card ≤ (insert v S).card := card_le_card (subset_insert _ _)
    have hcR : (S.card : ℝ) ≤ (insert v S).card := by exact_mod_cast hc
    linarith [h.1]
  · intro Z hZS hZ
    have hC := h.connected_delete Z hZ
    by_cases hvZ : v ∈ Z
    · convert hC using 1 <;> congr 1 <;> ext w <;> simp only [mem_coe, mem_sdiff, mem_insert] <;> grind
    · have hlt : Z.card < (nbr G S v).card := by exact_mod_cast hZ.trans_le hdeg
      obtain ⟨w,hw,hwZ⟩ := exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨hwS,hvw⟩ := mem_filter.mp hw
      have hsing : (G.induce ({v} : Set (Fin n))).Connected :=
        SimpleGraph.Connected.of_subsingleton
      have hh := G.connected_induce_union hC.preconnected hsing.preconnected
        (mem_sdiff.mpr ⟨hwS,hwZ⟩) (show v ∈ ({v} : Set (Fin n)) by simp)
        (G.adj_symm hvw)
      convert hh using 1 <;> congr 1 <;> ext x <;> simp only [mem_coe, mem_sdiff, mem_insert, Set.mem_union, Set.mem_singleton_iff] <;> grind

/-- Failure to merge two robust pieces supplies a small cross-edge separator. -/
theorem union_separator (hS : RealConnected G S t) (hT : RealConnected G T t)
    (hst : s ≤ t) (hnot : ¬RealConnected G (S ∪ T) s) :
    ∃ Z : Finset (Fin n), Z ⊆ S ∪ T ∧ (Z.card : ℝ)<s ∧
      (∀ u ∈ S \ Z, ∀ v ∈ T \ Z, ¬G.Adj u v) := by
  classical
  have hc : (S.card : ℝ) ≤ (S ∪ T).card := by
    exact_mod_cast card_le_card (subset_union_left : S ⊆ S ∪ T)
  have hsize : s ≤ ((S ∪ T).card : ℝ)-1 := by linarith [hS.1]
  have hn : ∃ Z : Finset (Fin n), Z ⊆ S ∪ T ∧ (Z.card : ℝ)<s ∧
      ¬(G.induce (↑((S ∪ T) \ Z) : Set (Fin n))).Connected := by
    by_contra! hh
    exact hnot ⟨hsize, hh⟩
  obtain ⟨Z,hZU,hZ,hdisc⟩ := hn
  refine ⟨Z,hZU,hZ,?_⟩
  intro u hu v hv huv
  have hSC := hS.connected_delete Z (hZ.trans_le hst)
  have hTC := hT.connected_delete Z (hZ.trans_le hst)
  have hh := G.connected_induce_union hSC.preconnected hTC.preconnected hu hv huv
  have he : (↑(S \ Z) : Set (Fin n)) ∪ ↑(T \ Z) = ↑((S ∪ T) \ Z) := by
    ext x
    simp only [mem_coe, Set.mem_union, mem_sdiff, mem_union]
    tauto
  apply hdisc
  convert hh using 1 <;> congr 1 <;> ext x <;> simp only [mem_coe, mem_sdiff, mem_union, Set.mem_union] <;> tauto

end RealConnected
end HadwigerRamsey.ControlledPartition
