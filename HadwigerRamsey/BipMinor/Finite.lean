import HadwigerRamsey.ThomasonUpper.Restriction
import HadwigerRamsey.Existence.MinorTools

open scoped BigOperators Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.BipMinor

def flip (i : Fin 2) : Fin 2 := if i=0 then 1 else 0
lemma eq_flip {i j : Fin 2} (h : i ≠ j) : j = flip i := by fin_cases i <;> fin_cases j <;> simp_all [flip]
lemma neighbors_subset {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (hp : ∀ u v, G.Adj u v → c u ≠ c v) (v : Fin n) :
    G.neighborFinset v ⊆ classVertices c (flip (c v)) := by
  intro w hw
  exact mem_filter.mpr ⟨mem_univ _,eq_flip (hp _ _ ((G.mem_neighborFinset _ _).mp hw))⟩
lemma degree_le {n a : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (hp : ∀ u v, G.Adj u v → c u ≠ c v)
    (hsize : ∀ i, (classVertices c i).card ≤ a) (v : Fin n) : G.degree v ≤ a :=
  (card_le_card (neighbors_subset G c hp v)).trans (hsize _)
lemma order_eq {n a : ℕ} (c : Fin n → Fin 2) (hsize : ∀ i, (classVertices c i).card = a) : n = 2*a := by
  have hh : ∑ i, (classVertices c i).card = n := by
    simpa [classVertices] using (card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ) (f := c) (fun _ _ => mem_univ _)).symm
  simpa [hsize] using hh.symm

/-- The total missing-degree budget controls a single round of pruning. -/
theorem low_degree_vertices_small {n a : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (ha : 0 < a) (hp : ∀ u v, G.Adj u v → c u ≠ c v)
    (hsize : ∀ i, (classVertices c i).card = a) {gamma : ℝ}
    (hedges : (1-gamma)*(a : ℝ)^2 ≤ G.edgeFinset.card) :
    ((univ.filter (fun v => (G.degree v : ℝ) < 7*(a : ℝ)/8)).card : ℝ) ≤ 16*gamma*a := by
  have hn := order_eq c hsize
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  let Z := univ.filter (fun v => (G.degree v : ℝ) < 7*(a : ℝ)/8)
  have hdef : ∀ v, 0 ≤ (a : ℝ)-G.degree v := fun v => by
    have hh : (G.degree v : ℝ) ≤ a := by exact_mod_cast degree_le G c hp (fun i => (hsize i).le) v
    linarith only [hh]
  have hsum : ∑ v : Fin n, ((a : ℝ)-G.degree v) = 2*(a : ℝ)^2-2*G.edgeFinset.card := by
    rw [sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,← Nat.cast_sum,G.sum_degrees_eq_twice_card_edges]
    simp only [hn,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hh : (Z.card : ℝ)*(a : ℝ)/8 ≤ ∑ v : Fin n, ((a : ℝ)-G.degree v) := by
    calc
      _ = ∑ _v ∈ Z, (a : ℝ)/8 := by simp; ring
      _ ≤ ∑ v ∈ Z, ((a : ℝ)-G.degree v) := sum_le_sum (fun v hv => by have hv' := (mem_filter.mp hv).2; linarith only [hv'])
      _ ≤ ∑ v : Fin n, ((a : ℝ)-G.degree v) := sum_le_sum_of_subset_of_nonneg (subset_univ Z) (fun v _ _ => hdef v)
  rw [hsum] at hh
  have he : (Z.card : ℝ)*(a : ℝ) ≤ (16*gamma*a)*(a : ℝ) := by nlinarith only [hh,hedges]
  exact (mul_le_mul_iff_left₀ haR).mp he

attribute [-instance] SimpleGraph.instDecidableComapAdj in
lemma restriction_degree {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n))
    (v : Fin (n-Z.card)) : G.degree (survivorMap Z v) ≤ (restrictedGraph G Z).degree v+Z.card := by
  have he : ((restrictedGraph G Z).neighborFinset v).image (survivorMap Z) = G.neighborFinset (survivorMap Z v) \ Z := by
    ext w
    simp only [mem_image,mem_sdiff,SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,survivorMap_not_mem Z u⟩
    · rintro ⟨hw,hz⟩
      obtain ⟨u,hu⟩ := (survivorEquiv Z).surjective ⟨w,hz⟩
      have hu' : survivorMap Z u = w := congrArg Subtype.val hu
      exact ⟨u,by change G.Adj (survivorMap Z v) (survivorMap Z u); simpa only [hu'] using hw,hu'⟩
  have hc := congrArg card he
  rw [card_image_of_injective _ (survivorMap_injective Z)] at hc
  have hh := card_le_card_sdiff_add_card (s := G.neighborFinset (survivorMap Z v)) (t := Z)
  simpa only [← hc,SimpleGraph.card_neighborFinset_eq_degree] using hh

lemma diagonal_interedges_empty {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (hp : ∀ u v, G.Adj u v → c u ≠ c v) (i : Fin 2) :
    G.interedges (classVertices c i) (classVertices c i) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hu,hv,huv⟩ := G.mem_interedges_iff.mp he
  exact hp _ _ huv (((mem_filter.mp hu).2).trans (mem_filter.mp hv).2.symm)
lemma cross_density {n a : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (hp : ∀ u v, G.Adj u v → c u ≠ c v) (hsize : ∀ i, (classVertices c i).card = a) :
    blockDensity G c 0 1 = (G.edgeFinset.card : ℝ)/(a : ℝ)^2 := by
  have hh := sum_card_block_interedges G c
  letI : Std.Symm G.Adj := G.symm
  have hcomm := Rel.card_interedges_comm (r := G.Adj) (classVertices c 0) (classVertices c 1)
  change (G.interedges (classVertices c 0) (classVertices c 1)).card = (G.interedges (classVertices c 1) (classVertices c 0)).card at hcomm
  simp only [Fin.sum_univ_two,diagonal_interedges_empty G c hp,card_empty,zero_add,add_zero] at hh
  have hcard : (G.interedges (classVertices c 0) (classVertices c 1)).card = G.edgeFinset.card := by omega
  simp only [blockDensity,show (0 : Fin 2) ≠ 1 by decide,if_false,SimpleGraph.edgeDensity_def,hsize,hcard]
  push_cast
  ring
end HadwigerRamsey.BipMinor
