import HadwigerRamsey.BipMinor.Finite
import HadwigerRamsey.ThomasonUpper.Connectivity

open scoped Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.BipMinor

/-- A deliberately weaker connectivity bound than the sharp bound in the
manuscript. Common neighbours survive any cut of fewer than a/4 vertices. -/
theorem connected_quarter {n a : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (ha : 0 < a) (han : a ≤ n)
    (hp : ∀ u v, G.Adj u v → c u ≠ c v)
    (hsize : ∀ i, (classVertices c i).card ≤ a)
    (hdeg : ∀ v, 3*(a : ℝ)/4 ≤ G.degree v) :
    VertexConnectedAtLeast G (a/4) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hd : (a/4 : ℕ) < n := by omega
  refine ⟨hd,?_⟩
  intro Z hZ
  have hZa : (Z.card : ℝ) < (a : ℝ)/4 := by
    have hh : 4*Z.card < a := by omega
    have hhR : 4*(Z.card : ℝ) < a := by exact_mod_cast hh
    linarith only [hhR]
  have hsame : ∀ u v : {v : Fin n // v ∉ Z}, c u = c v →
      (G.induce ((Z : Set (Fin n))ᶜ)).Reachable u v := by
    intro u v hc
    have hU : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ a := by
      apply le_trans (card_le_card (t := classVertices c (flip (c u))) ?_) (hsize _)
      intro w hw
      rcases mem_union.mp hw with hw | hw
      · exact neighbors_subset G c hp u hw
      · simpa only [hc] using neighbors_subset G c hp v hw
    have hI := card_inter_add_card_union (G.neighborFinset u) (G.neighborFinset v)
    have hIR : ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) +
        (G.neighborFinset u ∪ G.neighborFinset v).card = (G.degree u : ℝ)+G.degree v := by exact_mod_cast hI
    have hUR : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) ≤ a := by exact_mod_cast hU
    have hlt : Z.card < (G.neighborFinset u ∩ G.neighborFinset v).card := by
      have hh : (Z.card : ℝ) < (G.neighborFinset u ∩ G.neighborFinset v).card := by
        linarith only [hIR,hUR,hdeg u,hdeg v,hZa,haR]
      exact_mod_cast hh
    obtain ⟨w,hw,hwZ⟩ := exists_mem_notMem_of_card_lt_card hlt
    have huw : G.Adj u w := (G.mem_neighborFinset _ _).mp (mem_inter.mp hw).1
    have hvw : G.Adj v w := (G.mem_neighborFinset _ _).mp (mem_inter.mp hw).2
    exact (show (G.induce ((Z : Set (Fin n))ᶜ)).Adj u ⟨w,hwZ⟩ from huw).reachable.trans
      (show (G.induce ((Z : Set (Fin n))ᶜ)).Adj ⟨w,hwZ⟩ v from G.adj_symm hvw).reachable
  have hpre : (G.induce ((Z : Set (Fin n))ᶜ)).Preconnected := by
    intro u v
    by_cases hc : c u = c v
    · exact hsame u v hc
    · have hlt : Z.card < (G.neighborFinset v).card := by
        have hh : (Z.card : ℝ) < G.degree v := by linarith only [hdeg v,hZa,haR]
        exact_mod_cast hh
      obtain ⟨w,hw,hwZ⟩ := exists_mem_notMem_of_card_lt_card hlt
      have hvw := (G.mem_neighborFinset _ _).mp hw
      have he : c w = c u := (eq_flip (hp _ _ hvw)).trans (eq_flip (Ne.symm hc)).symm
      exact (hsame u ⟨w,hwZ⟩ he.symm).trans
        (show (G.induce ((Z : Set (Fin n))ᶜ)).Adj ⟨w,hwZ⟩ v from G.adj_symm hvw).reachable
  have hZn : Z.card < (univ : Finset (Fin n)).card := by simpa using hZ.trans hd
  obtain ⟨v,_,hv⟩ := exists_mem_notMem_of_card_lt_card hZn
  exact { preconnected := hpre, nonempty := ⟨⟨v,hv⟩⟩ }
end HadwigerRamsey.BipMinor
