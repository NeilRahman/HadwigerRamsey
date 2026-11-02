import HadwigerRamsey.ControlledPartition.Basic
import HadwigerRamsey.ControlledPartition.Decomposition

open Finset
open scoped Classical BigOperators
namespace HadwigerRamsey.TwoBigSets
open ControlledPartition

lemma interedges_card_sum {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    (G.interedges A B).card = ∑ v ∈ A, (nbr G B v).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := A)
    (fun e he => ((G.mem_interedges_iff).mp he).1)]
  apply sum_congr rfl
  intro v hv
  apply card_bij (fun e _ => e.2)
  · intro e he
    obtain ⟨he,heq⟩ := mem_filter.mp he
    obtain ⟨ha,hb,hadj⟩ := (G.mem_interedges_iff).mp he
    exact (mem_nbr _ _ _ _).mpr ⟨hb,heq ▸ hadj⟩
  · intro e he f hf hef
    exact Prod.ext ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm) hef
  · intro w hw
    exact ⟨(v,w),mem_filter.mpr ⟨(G.mem_interedges_iff).mpr
      ⟨hv,(mem_nbr G B v w).mp hw |>.1,(mem_nbr G B v w).mp hw |>.2⟩,rfl⟩,rfl⟩

lemma interedges_erase {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) {v : Fin n} (hv : v ∈ S) :
    (G.interedges S S).card ≤ (G.interedges (S.erase v) (S.erase v)).card +
      2*(nbr G S v).card := by
  classical
  let L := ({v} : Finset (Fin n)) ×ˢ nbr G S v
  let R := nbr G S v ×ˢ ({v} : Finset (Fin n))
  have hsub : G.interedges S S ⊆ G.interedges (S.erase v) (S.erase v) ∪ L ∪ R := by
    intro e he
    obtain ⟨he1,he2,ha⟩ := (G.mem_interedges_iff).mp he
    by_cases h1 : e.1 = v
    · apply mem_union_left
      apply mem_union_right
      exact mem_product.mpr ⟨mem_singleton.mpr h1,(mem_nbr _ _ _ _).mpr ⟨he2,h1 ▸ ha⟩⟩
    by_cases h2 : e.2 = v
    · apply mem_union_right
      exact mem_product.mpr ⟨(mem_nbr _ _ _ _).mpr ⟨he1,h2 ▸ G.adj_symm ha⟩,mem_singleton.mpr h2⟩
    · apply mem_union_left
      apply mem_union_left
      exact (G.mem_interedges_iff).mpr ⟨mem_erase.mpr ⟨h1,he1⟩,
        mem_erase.mpr ⟨h2,he2⟩,ha⟩
  have hh := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  simpa only [L,R,card_product,card_singleton,one_mul,mul_one,two_mul,add_assoc] using hh

lemma degenerate_ordered {n : ℕ} (G : SimpleGraph (Fin n)) {d : ℝ}
    {Y : Finset (Fin n)} (hdeg : DegenerateOn G Y d) :
    ((G.interedges Y Y).card : ℝ) ≤ 2*d*Y.card := by
  classical
  revert hdeg
  refine Finset.strongInductionOn Y ?_
  intro Y ih hdeg
  by_cases hy : Y.Nonempty
  · obtain ⟨v,hv,hd⟩ := hdeg Y Subset.rfl hy
    have hde := hdeg.mono (erase_subset v Y) le_rfl
    have hc := ih (Y.erase v) (erase_ssubset hv) hde
    have he : ((G.interedges Y Y).card : ℝ) ≤
        (G.interedges (Y.erase v) (Y.erase v)).card + 2*(nbr G Y v).card := by
      exact_mod_cast interedges_erase G Y hv
    have hcard : ((Y.erase v).card : ℝ)+1=Y.card := by exact_mod_cast card_erase_add_one hv
    have hprod := congrArg (fun x : ℝ => 2*d*x) hcard
    nlinarith only [hc,he,hd,hprod]
  · have hY := not_nonempty_iff_eq_empty.mp hy
    simp [hY]
lemma ordered_univ {n : ℕ} (G : SimpleGraph (Fin n)) :
    (G.interedges univ univ).card = 2*G.edgeFinset.card := by
  simpa [SimpleGraph.interedges_def,Rel.interedges] using G.two_mul_card_edgeFinset.symm

lemma edges_le_of_degenerate {n : ℕ} (G : SimpleGraph (Fin n))
    {Y : Finset (Fin n)} {d : ℝ} (hdeg : DegenerateOn G Y d) (hd : 0 ≤ d) :
    (G.edgeFinset.card : ℝ) ≤ d*n + ((n-Y.card : ℕ) : ℝ)*n := by
  classical
  let Z := univ \ Y
  have hcover : G.interedges univ univ ⊆ G.interedges Y Y ∪
      G.interedges Z univ ∪ G.interedges univ Z := by
    intro e he
    obtain ⟨_,_,ha⟩ := (G.mem_interedges_iff).mp he
    by_cases h1 : e.1 ∈ Y
    · by_cases h2 : e.2 ∈ Y
      · exact mem_union_left _ (mem_union_left _ ((G.mem_interedges_iff).mpr ⟨h1,h2,ha⟩))
      · exact mem_union_right _ ((G.mem_interedges_iff).mpr ⟨mem_univ _,by simp [Z,h2],ha⟩)
    · exact mem_union_left _ (mem_union_right _ ((G.mem_interedges_iff).mpr ⟨by simp [Z,h1],mem_univ _,ha⟩))
  have hh := (card_le_card hcover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have h1 := G.card_interedges_le_mul Z univ
  have h2 := G.card_interedges_le_mul univ Z
  have hZ : Z.card = n-Y.card := by
    dsimp [Z]
    rw [card_sdiff_of_subset (subset_univ Y)]
    simp
  have hr : (2*G.edgeFinset.card : ℝ) ≤ (G.interedges Y Y).card +
      2*((n-Y.card : ℕ):ℝ)*n := by
    rw [ordered_univ] at hh
    rw [card_univ,Fintype.card_fin,hZ] at h1 h2
    have hh' := hh.trans (Nat.add_le_add (Nat.add_le_add_left h1 _) h2)
    have hhR : (2*G.edgeFinset.card : ℝ) ≤ (G.interedges Y Y).card + ((n-Y.card:ℕ):ℝ)*n + (n:ℝ)*((n-Y.card:ℕ):ℝ) := by exact_mod_cast hh'
    nlinarith only [hhR]
  have hdeg' := degenerate_ordered G hdeg
  have hYn : (Y.card : ℝ) ≤ n := by exact_mod_cast (by simpa using Y.card_le_univ : Y.card ≤ n)
  have hhdeg := mul_le_mul_of_nonneg_left hYn hd
  nlinarith only [hr,hdeg',hhdeg]

lemma remainder_small {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    {Y : Finset (Fin n)} {r ε : ℝ} (hr : 0 ≤ r) (hre : r ≤ 2*ε/3)
    (hdeg : DegenerateOn G Y (3*r*n))
    (hdense : 3*ε*(n : ℝ)^2 < G.edgeFinset.card) :
    (Y.card : ℝ) < (1-ε)*n := by
  have hh := edges_le_of_degenerate G hdeg (by positivity)
  have hYn : Y.card ≤ n := by simpa using Y.card_le_univ
  have hc : ((n-Y.card : ℕ):ℝ) = (n:ℝ)-Y.card := by rw [Nat.cast_sub hYn]
  rw [hc] at hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h : 3*r ≤ 2*ε := by linarith
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (n:ℝ))
  by_contra! hbad
  have hm2 := mul_le_mul_of_nonneg_right hbad hnR.le
  nlinarith only [hh,hdense,hm,hm2]

lemma cross_le_controlled {n : ℕ} (G : SimpleGraph (Fin n)) (P : Decomposition n)
    {r η δ : ℝ} (hP : Controlled G r η δ P) (hη : 0 ≤ η)
    (S T A B : Finset (Fin n)) (hS : S ∈ P.parts ∨ S = P.Y)
    (hT : T ∈ P.parts ∨ T = P.Y) (hST : S ≠ T)
    (hAS : A ⊆ S) (hBT : B ⊆ T) (hAB : A.card = B.card) :
    ((G.interedges A B).card : ℝ) ≤ η*n*A.card := by
  classical
  have bound : ∀ U W, U ⊆ P.Y → W ⊆ P.core →
      ((G.interedges U W).card : ℝ) ≤ η*n*U.card := by
    intro U W hUY hWC
    rw [interedges_card_sum, Nat.cast_sum]
    calc
      _ ≤ ∑ _v ∈ U, η*n := sum_le_sum (by
        intro v hv
        have hh : ((nbr G W v).card:ℝ) ≤ (nbr G P.core v).card := by
          exact_mod_cast card_le_card (nbr_mono G hWC v)
        exact hh.trans (hP.2.2.2.1 v (hUY hv)))
      _ = _ := by simp; ring
  rcases hS with hS | rfl <;> rcases hT with hT | rfl
  · have he : G.interedges A B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨ha,hb,hadj⟩ := (G.mem_interedges_iff).mp he
      exact hP.2.2.2.2.2 S hS T hT hST e.1 (hAS ha) e.2 (hBT hb) hadj
    rw [he,card_empty,Nat.cast_zero]
    positivity
  · have hh := bound B A hBT (hAS.trans (P.subset_core hS))
    letI : Std.Symm G.Adj := G.symm
    have he := Rel.card_interedges_comm (r := G.Adj) A B
    change (G.interedges A B).card = (G.interedges B A).card at he
    simpa only [he,hAB] using hh
  · exact bound A B hAS (hBT.trans (P.subset_core hT))
  · exact (hST rfl).elim

end HadwigerRamsey.TwoBigSets
