import HadwigerRamsey.DenseMinor.Cut
import HadwigerRamsey.Decomposition

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper

namespace HadwigerRamsey.TwoBigSets

lemma cross_count_sum {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (A B : Finset (Fin n)) (hdis : Disjoint A B) :
    ∑ i : Fin 3, ((G i).interedges A B).card = A.card*B.card := by
  classical
  have he : univ.biUnion (fun i : Fin 3 => (G i).interedges A B) = A ×ˢ B := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, SimpleGraph.mem_interedges_iff,mem_product]
    constructor
    · rintro ⟨i,ha,hb,_⟩; exact ⟨ha,hb⟩
    · rintro ⟨ha,hb⟩
      obtain ⟨i,hi,_⟩ := hG e.1 e.2 (hdis.forall_ne_finset ha hb)
      exact ⟨i,ha,hb,hi⟩
  have hd : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint (fun i => (G i).interedges A B) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro e hei hej
    obtain ⟨ha,hb,hi⟩ := Rel.mem_interedges_iff.mp hei
    obtain ⟨_,_,hj⟩ := Rel.mem_interedges_iff.mp hej
    obtain ⟨c,hc,hu⟩ := hG e.1 e.2 (hdis.forall_ne_finset ha hb)
    exact hij ((hu i hi).trans (hu j hj).symm)
  rw [← card_biUnion hd,he,card_product]

lemma third_cross_lower {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (hAB : A.card = B.card)
    (η : ℝ)
    (hi : (((G i).interedges A B).card : ℝ) ≤ η*n*A.card)
    (hj : (((G j).interedges A B).card : ℝ) ≤ η*n*A.card) :
    (A.card : ℝ)^2 - 2*η*n*A.card ≤ ((G k).interedges A B).card := by
  have hs := cross_count_sum G hG A B hdis
  have hsum : ((G i).interedges A B).card + ((G j).interedges A B).card +
      ((G k).interedges A B).card = A.card * A.card := by
    rw [← hAB] at hs
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [Fin.sum_univ_three] <;> omega
  have hr : (((G i).interedges A B).card : ℝ) + ((G j).interedges A B).card +
      ((G k).interedges A B).card = (A.card : ℝ)^2 := by
    rw [pow_two]
    exact_mod_cast hsum
  linarith only [hr,hi,hj]

attribute [-instance] SimpleGraph.instDecidableComapAdj in
lemma interedges_comap_image {n m : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin m → Fin n) (hf : Function.Injective f) (A B : Finset (Fin m)) :
    ((G.comap f).interedges A B).card = (G.interedges (A.image f) (B.image f)).card := by
  classical
  apply card_bij (fun e _ => (f e.1,f e.2))
  · intro e he
    obtain ⟨ha,hb,h⟩ := Rel.mem_interedges_iff.mp he
    exact Rel.mem_interedges_iff.mpr ⟨mem_image_of_mem f ha,mem_image_of_mem f hb,h⟩
  · intro e _ d _ h
    exact Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  · intro e he
    obtain ⟨ha,hb,h⟩ := Rel.mem_interedges_iff.mp he
    obtain ⟨u,hu,he_u⟩ := mem_image.mp ha
    obtain ⟨v,hv,he_v⟩ := mem_image.mp hb
    refine ⟨(u,v),Rel.mem_interedges_iff.mpr ⟨hu,hv,?_⟩,?_⟩
    · change G.Adj (f u) (f v)
      simpa only [he_u,he_v] using h
    · exact Prod.ext he_u he_v

attribute [-instance] SimpleGraph.instDecidableComapAdj in
/-- Apply the public balanced bipartite theorem to the cross edges of two sets. -/
theorem cross_minor {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (hAB : A.card = B.card)
    {K γ : ℝ} {N : ℕ} (hN : N ≤ A.card)
    (hbip : ∀ m : ℕ, ∀ H : SimpleGraph (Fin m), ∀ X Y : Finset (Fin m),
      H.IsBipartiteWith (X : Set (Fin m)) (Y : Set (Fin m)) →
      X ∪ Y = univ → X.card = Y.card → N ≤ X.card →
      (1-γ)*(X.card : ℝ)^2 ≤ H.edgeFinset.card →
      K*(X.card : ℝ)/sqrt (log (X.card : ℝ)) ≤ (hadwigerNumber H : ℝ))
    (hdensity : (1-γ)*(A.card : ℝ)^2 ≤ (G.interedges A B).card) :
    K*(A.card : ℝ)/sqrt (log (A.card : ℝ)) ≤ (hadwigerNumber G : ℝ) := by
  classical
  let S := A ∪ B
  let f : Fin S.card → Fin n := fun i => (S.equivFin.symm i).val
  have hf : Function.Injective f := by
    intro i j h
    exact S.equivFin.symm.injective (Subtype.ext h)
  let c : Fin S.card → Fin 2 := fun v => if f v ∈ A then 0 else 1
  let AA := classVertices c 0
  let BB := classVertices c 1
  have hAim : AA.image f = A := by
    ext v
    constructor
    · rintro hv
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
      simpa [AA,classVertices,c] using hu
    · intro hv
      have hvS : v ∈ S := mem_union_left _ hv
      refine mem_image.mpr ⟨S.equivFin ⟨v,hvS⟩,?_,by simp [f]⟩
      simp [AA,classVertices,c,f,hv]
  have hBim : BB.image f = B := by
    ext v
    constructor
    · intro hv
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
      have huA : f u ∉ A := by simpa [BB,classVertices,c] using hu
      have huS := (S.equivFin.symm u).property
      exact (mem_union.mp huS).resolve_left huA
    · intro hv
      have hvA : v ∉ A := fun h => disjoint_left.mp hdis h hv
      have hvS : v ∈ S := mem_union_right _ hv
      refine mem_image.mpr ⟨S.equivFin ⟨v,hvS⟩,?_,by simp [f]⟩
      simp [BB,classVertices,c,f,hvA]
  have hAA : AA.card = A.card := by rw [←hAim,card_image_of_injective _ hf]
  have hBB : BB.card = A.card := by
    have hh : BB.card = B.card := by rw [←hBim,card_image_of_injective _ hf]
    exact hh.trans hAB.symm
  let H := DenseMinor.cutGraph (G.comap f) c
  have hcut : H.edgeFinset.card = (G.interedges A B).card := by
    rw [DenseMinor.cut_card (G.comap f) c (a := A.card) (by
      intro i
      fin_cases i
      · exact hAA
      · exact hBB)]
    rw [interedges_comap_image G f hf, hAim,hBim]
  have hbound := hbip S.card H AA BB
    (DenseMinor.cut_bipartite (G.comap f) c) (DenseMinor.classes_cover c)
    (hAA.trans hBB.symm) (by simpa only [hAA] using hN) (by simpa only [hAA,hcut] using hdensity)
  have hHG : hadwigerNumber H ≤ hadwigerNumber G := by
    apply le_trans ?_ (hadwigerNumber_comap_le G f hf)
    apply cliqueMinor_le_hadwigerNumber
    exact (hadwigerNumber_hasCliqueMinor H).map_injective
      (SimpleGraph.Hom.ofLE (DenseMinor.cutGraph_le (G.comap f) c)) Function.injective_id
  have hHGreal : (hadwigerNumber H : ℝ) ≤ hadwigerNumber G := by exact_mod_cast hHG
  have hbound' : K*(A.card : ℝ)/sqrt (log (A.card : ℝ)) ≤ (hadwigerNumber H : ℝ) := by
    simpa only [hAA] using hbound
  exact hbound'.trans hHGreal

end HadwigerRamsey.TwoBigSets
