import HadwigerRamsey.ControlledPartition.Interpretation
import HadwigerRamsey.TwoBigSets.Finite
import HadwigerRamsey.ThomasonUpper.Density

open Finset Real
open scoped Classical BigOperators

namespace HadwigerRamsey.Main
open ControlledPartition ThomasonUpper

/-- The indexed partition used in the final optimization, including its last exceptional class. -/
structure PartitionData {n : ℕ} (G : SimpleGraph (Fin n)) (lam η δ : ℝ) where
  m : ℕ
  V : Fin (m+1) → Finset (Fin n)
  pairwise : Pairwise (fun i j => Disjoint (V i) (V j))
  cover : univ.biUnion V = univ
  active_size : ∀ i : Fin m, lam*n ≤ ((V i.castSucc).card : ℝ)
  dummy_size : ((V (Fin.last m)).card : ℝ) ≤ 21*lam*n
  count : (m+1 : ℝ) ≤ 2/lam
  active_kind : ∀ i : Fin m,
    RealConnected G (V i.castSucc) (δ*n) ∨
      (DegenerateOn G (V i.castSucc) (3*lam*n) ∧ 20*lam*n ≤ ((V i.castSucc).card : ℝ))
  cross : ∀ i j : Fin m, i ≠ j →
    (G.edgeDensity (V i.castSucc) (V j.castSucc) : ℝ) ≤ η/lam

/-- Label a disjoint covering family, allowing its exceptional class to be empty. -/
theorem exists_classMap {n k : ℕ} (V : Fin k → Finset (Fin n))
    (hdis : Pairwise (fun i j => Disjoint (V i) (V j)))
    (hc : univ.biUnion V = univ) :
    ∃ τ : Fin n → Fin k, ∀ i, classVertices τ i = V i := by
  classical
  have hex : ∀ v : Fin n, ∃ i, v ∈ V i := by
    intro v
    have hv : v ∈ univ.biUnion V := by rw [hc]; simp
    simpa only [mem_biUnion, mem_univ, true_and] using hv
  choose τ hτ using hex
  refine ⟨τ,?_⟩
  intro i
  ext v
  simp only [classVertices,mem_filter,mem_univ,true_and]
  constructor
  · intro hv
    exact hv ▸ hτ v
  · intro hv
    by_contra hne
    exact disjoint_left.mp (hdis hne) (hτ v) hv

/-- Indexed enumeration of an ordinary finite family with a distinguished last class. -/
theorem index_family {n : ℕ} (F : Finset (Finset (Fin n))) (D : Finset (Fin n))
    (hF : (F : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hD : ∀ S ∈ F, Disjoint S D) (hcover : F.biUnion id ∪ D = univ) :
    ∃ V : Fin (F.card+1) → Finset (Fin n),
      (∀ i : Fin F.card, V i.castSucc = (F.equivFin.symm i).val) ∧
      V (Fin.last F.card) = D ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧ univ.biUnion V = univ := by
  classical
  let f : Fin F.card → Finset (Fin n) := fun i => (F.equivFin.symm i).val
  let V : Fin (F.card+1) → Finset (Fin n) := Fin.lastCases D f
  have hV : ∀ i : Fin F.card, V i.castSucc = f i := by intro i; simp [V]
  have hlast : V (Fin.last F.card) = D := by simp [V]
  have hf : ∀ i : Fin F.card, f i ∈ F := fun i => (F.equivFin.symm i).property
  refine ⟨V,hV,hlast,?_,?_⟩
  · intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩ | rfl
    · rw [hV,hV]
      apply hF (hf i) (hf j)
      intro he
      have hsame : i=j := F.equivFin.symm.injective (Subtype.ext he)
      exact hij (congrArg Fin.castSucc hsame)
    · rw [hV,hlast]
      exact hD _ (hf i)
    · rw [hlast,hV]
      exact (hD _ (hf j)).symm
    · exact (hij rfl).elim
  · ext v
    constructor
    · intro _; simp
    · intro _
      have hv : v ∈ F.biUnion id ∪ D := by rw [hcover]; simp
      rcases mem_union.mp hv with hv | hv
      · obtain ⟨S,hS,hvS⟩ := mem_biUnion.mp hv
        refine mem_biUnion.mpr ⟨(F.equivFin ⟨S,hS⟩).castSucc,mem_univ _,?_⟩
        rw [hV]
        simpa only [f,Equiv.symm_apply_apply,id_eq] using hvS
      · exact mem_biUnion.mpr ⟨Fin.last F.card,mem_univ _,hlast.symm ▸ hv⟩

lemma controlled_cross_density {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Decomposition n) {lam η δ : ℝ} (hn : 0 < n) (hlam : 0 < lam) (hη : 0 ≤ η)
    (hP : Controlled G lam η δ P) (S T : Finset (Fin n))
    (hS : S ∈ P.parts ∨ S = P.Y) (hT : T ∈ P.parts ∨ T = P.Y)
    (hST : S ≠ T) (hScard : lam*n ≤ (S.card : ℝ)) (hTcard : lam*n ≤ (T.card : ℝ)) :
    (G.edgeDensity S T : ℝ) ≤ η/lam := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < S.card := (mul_pos hlam hnR).trans_le hScard
  have ht : (0 : ℝ) < T.card := (mul_pos hlam hnR).trans_le hTcard
  have bound : ∀ U W : Finset (Fin n), U ⊆ P.Y → W ⊆ P.core →
      ((G.interedges U W).card : ℝ) ≤ η*n*U.card := by
    intro U W hUY hWC
    rw [TwoBigSets.interedges_card_sum,Nat.cast_sum]
    calc
      _ ≤ ∑ _v ∈ U, η*n := sum_le_sum (by
        intro v hv
        have hh : ((nbr G W v).card:ℝ) ≤ (nbr G P.core v).card := by
          exact_mod_cast card_le_card (nbr_mono G hWC v)
        exact hh.trans (hP.2.2.2.1 v (hUY hv)))
      _ = _ := by simp; ring
  have count_bound : ((G.interedges S T).card : ℝ)*lam ≤ η*(S.card : ℝ)*T.card := by
    rcases hS with hS | rfl <;> rcases hT with hT | rfl
    · have he : G.interedges S T = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨ha,hb,hadj⟩ := (G.mem_interedges_iff).mp he
        exact hP.2.2.2.2.2 S hS T hT hST e.1 ha e.2 hb hadj
      rw [he,card_empty,Nat.cast_zero,zero_mul]
      positivity
    · have hh := bound P.Y S Subset.rfl (P.subset_core hS)
      letI : Std.Symm G.Adj := G.symm
      have he := Rel.card_interedges_comm (r := G.Adj) S P.Y
      change (G.interedges S P.Y).card = (G.interedges P.Y S).card at he
      have hh' : ((G.interedges S P.Y).card : ℝ) ≤ η*n*P.Y.card := by
        simpa only [he] using hh
      have hm := mul_le_mul_of_nonneg_right hh' hlam.le
      have hm' := mul_le_mul_of_nonneg_right hScard (mul_nonneg hη (Nat.cast_nonneg P.Y.card))
      nlinarith only [hm,hm']
    · have hh := bound P.Y T Subset.rfl (P.subset_core hT)
      have hm := mul_le_mul_of_nonneg_right hh hlam.le
      have hm' := mul_le_mul_of_nonneg_right hTcard (mul_nonneg hη (Nat.cast_nonneg P.Y.card))
      nlinarith only [hm,hm']
    · exact (hST rfl).elim
  simp only [SimpleGraph.edgeDensity_def,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]
  exact (div_le_div_iff₀ (mul_pos hs ht) hlam).mpr (by nlinarith only [count_bound])


/-- Build the last exceptional class and optionally retain the large degenerate remainder. -/
theorem partitionData_exists {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Decomposition n) {lam η δ : ℝ} (hn : 0 < n) (hlam : 0 < lam)
    (hlamsmall : lam ≤ 1/100) (hη : 0 ≤ η) (hP : Controlled G lam η δ P) :
    Nonempty (PartitionData G lam η δ) := by
  classical
  let F := if 20*lam*n ≤ (P.Y.card : ℝ) then insert P.Y P.parts else P.parts
  let D := if 20*lam*n ≤ (P.Y.card : ℝ) then P.X else P.X ∪ P.Y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlamn : 0 < lam*(n : ℝ) := mul_pos hlam hnR
  have horigin : ∀ S ∈ F, S ∈ P.parts ∨ S = P.Y := by
    intro S hS
    by_cases hlarge : 20*lam*n ≤ (P.Y.card : ℝ)
    · exact (mem_insert.mp (by simpa only [F,if_pos hlarge] using hS)).symm
    · exact Or.inl (by simpa only [F,if_neg hlarge] using hS)
  have hsize : ∀ S ∈ F, lam*n ≤ (S.card : ℝ) := by
    intro S hS
    by_cases hlarge : 20*lam*n ≤ (P.Y.card : ℝ)
    · have hs : S = P.Y ∨ S ∈ P.parts := by simpa only [F,if_pos hlarge,mem_insert] using hS
      rcases hs with rfl | hS
      · nlinarith only [hlarge,hlamn]
      · exact hP.2.2.2.2.1 S hS
    · exact hP.2.2.2.2.1 S (by simpa only [F,if_neg hlarge] using hS)
  have hFpair : (F : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro S hS T hT hST
    rcases horigin S hS with hS | rfl <;> rcases horigin T hT with hT | rfl
    · exact P.pairwise hS hT hST
    · exact P.disjoint_Y S hS
    · exact (P.disjoint_Y T hT).symm
    · exact (hST rfl).elim
  have hD : ∀ S ∈ F, Disjoint S D := by
    intro S hS
    by_cases hlarge : 20*lam*n ≤ (P.Y.card : ℝ)
    · rw [show D = P.X from if_pos hlarge]
      rcases horigin S hS with hS | rfl
      · exact P.disjoint_X S hS
      · exact P.disjoint_XY.symm
    · rw [show D = P.X ∪ P.Y from if_neg hlarge]
      have hs : S ∈ P.parts := by simpa only [F,if_neg hlarge] using hS
      exact disjoint_union_right.mpr ⟨P.disjoint_X S hs,P.disjoint_Y S hs⟩
  have hcover : F.biUnion id ∪ D = univ := by
    by_cases hlarge : 20*lam*n ≤ (P.Y.card : ℝ)
    · simpa only [F,D,if_pos hlarge,biUnion_insert,id_eq,
        union_assoc,union_left_comm,union_comm] using P.cover
    · simpa only [F,D,if_neg hlarge,union_assoc] using P.cover
  have hdsize : (D.card : ℝ) ≤ 21*lam*n := by
    by_cases hlarge : 20*lam*n ≤ (P.Y.card : ℝ)
    · have he : D = P.X := if_pos hlarge
      rw [he]
      nlinarith only [hP.1,hlamn]
    · have he : D = P.X ∪ P.Y := if_neg hlarge
      have hc : (D.card : ℝ) ≤ P.X.card + (P.Y.card : ℝ) := by
        rw [he]
        exact_mod_cast card_union_le P.X P.Y
      have hh : (P.Y.card : ℝ) < 20*lam*n := lt_of_not_ge hlarge
      nlinarith only [hc,hP.1,hh]
  have hcount : F.card ≤ P.parts.card+1 := by
    by_cases hlarge : 20*lam*n ≤ (P.Y.card : ℝ)
    · simpa only [F,if_pos hlarge] using card_insert_le P.Y P.parts
    · simp only [F,if_neg hlarge]; omega
  have hbound := Controlled.card_parts_le hP hn hlam
  have hcountR : (F.card : ℝ) ≤ (P.parts.card : ℝ)+1 := by exact_mod_cast hcount
  have hcountfinal : (F.card+1 : ℝ) ≤ 2/lam := by
    have hh := mul_le_mul_of_nonneg_right hbound hlam.le
    simp only [inv_mul_cancel₀ hlam.ne'] at hh
    apply (le_div_iff₀ hlam).mpr
    nlinarith only [hh,hcountR,hlamsmall,hlam]
  have hkind : ∀ S ∈ F, RealConnected G S (δ*n) ∨
      (DegenerateOn G S (3*lam*n) ∧ 20*lam*n ≤ (S.card : ℝ)) := by
    intro S hS
    by_cases hs : S ∈ P.parts
    · exact Or.inl (hP.2.1 S hs)
    · have he : S=P.Y := (horigin S hS).resolve_left hs
      subst S
      have hlarge : 20*lam*n ≤ (P.Y.card : ℝ) := by
        by_contra hh
        exact hs (by simpa only [F,if_neg hh] using hS)
      exact Or.inr ⟨hP.2.2.1,hlarge⟩
  obtain ⟨V,hV,hlast,hpair,hcov⟩ := index_family F D hFpair hD hcover
  refine ⟨⟨F.card,V,hpair,hcov,?_,?_,hcountfinal,?_,?_⟩⟩
  · intro i
    rw [hV]
    exact hsize _ (F.equivFin.symm i).property
  · simpa only [hlast] using hdsize
  · intro i
    rw [hV]
    exact hkind _ (F.equivFin.symm i).property
  · intro i j hij
    rw [hV,hV]
    apply controlled_cross_density G P hn hlam hη hP
    · exact horigin _ (F.equivFin.symm i).property
    · exact horigin _ (F.equivFin.symm j).property
    · intro he
      exact hij (F.equivFin.symm.injective (Subtype.ext he))
    · exact hsize _ (F.equivFin.symm i).property
    · exact hsize _ (F.equivFin.symm j).property


noncomputable def PartitionData.classes {n : ℕ} {G : SimpleGraph (Fin n)}
    {lam η δ : ℝ} (P : PartitionData G lam η δ) : Fin n → Fin (P.m+1) :=
  Classical.choose (exists_classMap P.V P.pairwise P.cover)

@[simp] theorem PartitionData.classVertices_classes {n : ℕ} {G : SimpleGraph (Fin n)}
    {lam η δ : ℝ} (P : PartitionData G lam η δ) (i : Fin (P.m+1)) :
    classVertices P.classes i = P.V i :=
  Classical.choose_spec (exists_classMap P.V P.pairwise P.cover) i


theorem PartitionData.m_pos {n : ℕ} {G : SimpleGraph (Fin n)}
    {lam η δ : ℝ} (P : PartitionData G lam η δ) (hn : 0 < n)
    (hlam : 0 < lam) (hlamsmall : lam ≤ 1/100) : 0 < P.m := by
  classical
  apply Nat.pos_of_ne_zero
  intro hz
  have hwhole : P.V (Fin.last P.m) = univ := by
    ext v
    constructor
    · intro _; simp
    · intro _
      have hv : v ∈ univ.biUnion P.V := by rw [P.cover]; simp
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
      have he : i=Fin.last P.m := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      simpa only [he] using hi
  have hd := P.dummy_size
  rw [hwhole,card_univ,Fintype.card_fin] at hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_right hlamsmall hnR.le
  nlinarith only [hd,hh,hnR]

end HadwigerRamsey.Main
