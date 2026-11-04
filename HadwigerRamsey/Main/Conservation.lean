import HadwigerRamsey.Decomposition
import HadwigerRamsey.TwoBigSets.Minor
import HadwigerRamsey.ThomasonUpper.Density

open scoped Classical BigOperators
open Finset Real

namespace HadwigerRamsey.Main
open ThomasonUpper

lemma sum_three_distinct {R : Type*} [AddCommMonoid R] (f : Fin 3 → R)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    f i+f j+f k = ∑ c, f c := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [Fin.sum_univ_three] <;> abel

lemma ordered_diagonal_sum {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (S : Finset (Fin n)) :
    ∑ c : Fin 3, ((G c).interedges S S).card = S.card*(S.card-1) := by
  classical
  have he : univ.biUnion (fun c : Fin 3 => (G c).interedges S S) = S.offDiag := by
    ext e
    simp only [mem_biUnion,mem_univ,true_and,SimpleGraph.mem_interedges_iff,mem_offDiag]
    constructor
    · rintro ⟨c,hu,hv,hadj⟩
      refine ⟨hu,hv,?_⟩
      intro hh
      exact (G c).irrefl (by simpa only [hh] using hadj)
    · rintro ⟨hu,hv,hne⟩
      obtain ⟨c,hc,_⟩ := hG e.1 e.2 hne
      exact ⟨c,hu,hv,hc⟩
  have hdis : (Set.univ : Set (Fin 3)).PairwiseDisjoint (fun c => (G c).interedges S S) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro e hei hej
    obtain ⟨hu,hv,hi⟩ := ((G i).mem_interedges_iff).mp hei
    obtain ⟨_,_,hj⟩ := ((G j).mem_interedges_iff).mp hej
    have hne : e.1 ≠ e.2 := fun hh => (G i).irrefl (by simpa only [hh] using hi)
    obtain ⟨c,hc,hunique⟩ := hG e.1 e.2 hne
    exact hij ((hunique i hi).trans (hunique j hj).symm)
  have hdis' : ((univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun c => (G c).interedges S S) := by simpa using hdis
  rw [←card_biUnion hdis',he,offDiag_card,Nat.mul_sub_left_distrib,mul_one]

lemma diagonal_density_sum {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∑ c : Fin 3, internalDensity (G c) S = 1 := by
  classical
  have hh := ordered_diagonal_sum G hG S
  simp_rw [card_internal_interedges] at hh
  have he : (∑ c : Fin 3, ((G c).induce (S : Set (Fin n))).edgeFinset.card : ℝ) =
      (S.card.choose 2 : ℝ) := by
    have hreal : 2*(∑ c : Fin 3, (((G c).induce (S : Set (Fin n))).edgeFinset.card : ℝ)) =
        (S.card : ℝ)*(S.card-1) := by
      have hcast : (∑ c : Fin 3, (2*(((G c).induce (S : Set (Fin n))).edgeFinset.card : ℝ))) =
          (S.card : ℝ)*(S.card-1) := by
        have hc := congrArg (fun z : ℕ => (z : ℝ)) hh
        simpa only [Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat,
          Nat.cast_sub (by omega : 1 ≤ S.card),Nat.cast_one] using hc
      simpa only [sum_mul,Finset.mul_sum] using hcast
    rw [Nat.cast_choose_two]
    nlinarith only [hreal]
  have hden : (0 : ℝ) < S.card.choose 2 := by exact_mod_cast Nat.choose_pos hS
  simp only [internalDensity,←sum_div]
  rw [he,div_self hden.ne']

lemma diagonal_conservation {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    internalDensity (G i) S+internalDensity (G j) S+internalDensity (G k) S = 1 := by
  rw [sum_three_distinct (fun c => internalDensity (G c) S) i j k hij hik hjk]
  exact diagonal_density_sum G hG S hS

lemma offdiagonal_conservation {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (S T : Finset (Fin n))
    (hdis : Disjoint S T) (hS : S.Nonempty) (hT : T.Nonempty)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (G i).edgeDensity S T+(G j).edgeDensity S T+(G k).edgeDensity S T = (1 : ℚ) := by
  classical
  have hs := TwoBigSets.cross_count_sum G hG S T hdis
  have hsum : ((G i).interedges S T).card+((G j).interedges S T).card+
      ((G k).interedges S T).card = S.card*T.card := by
    rw [sum_three_distinct (fun c => ((G c).interedges S T).card) i j k hij hik hjk]
    exact hs
  have hn : (S.card : ℚ)*T.card ≠ 0 := by
    have hs : (0 : ℚ) < S.card := by exact_mod_cast hS.card_pos
    have ht : (0 : ℚ) < T.card := by exact_mod_cast hT.card_pos
    positivity
  simp only [SimpleGraph.edgeDensity_def]
  rw [←add_div,←add_div]
  have hsumR : (((G i).interedges S T).card : ℚ)+((G j).interedges S T).card+
      ((G k).interedges S T).card = S.card*T.card := by exact_mod_cast hsum
  rw [hsumR,div_self hn]

lemma restricted_diagonal_conservation {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (S P Q : Finset (Fin n)) (hS : 2 ≤ S.card)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {d ξ : ℝ}
    (hP : internalDensity (G i) S-d ≤ internalDensity (G i) (S ∩ P))
    (hQ : internalDensity (G j) S-d ≤ internalDensity (G j) (S ∩ Q))
    (hd : 2*d ≤ ξ) :
    1-ξ ≤ internalDensity (G k) S+internalDensity (G i) (S ∩ P)+
      internalDensity (G j) (S ∩ Q) := by
  have hh := diagonal_conservation G hG S hS i j k hij hik hjk
  linarith

lemma restricted_offdiagonal_conservation {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (S T P Q : Finset (Fin n))
    (hdis : Disjoint S T) (hS : S.Nonempty) (hT : T.Nonempty)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {d e ξ : ℝ}
    (hP : (G i).edgeDensity S T-d ≤ ((G i).edgeDensity (S ∩ P) (T ∩ P) : ℝ))
    (hQ : (G j).edgeDensity S T-d ≤ ((G j).edgeDensity (S ∩ Q) (T ∩ Q) : ℝ))
    (hc : ((G k).edgeDensity S T : ℝ) ≤ e) (hd : e+2*d ≤ ξ) :
    1-ξ ≤ ((G i).edgeDensity (S ∩ P) (T ∩ P) : ℝ)+
      ((G j).edgeDensity (S ∩ Q) (T ∩ Q) : ℝ) := by
  have hh : ((G i).edgeDensity S T : ℝ)+((G j).edgeDensity S T : ℝ)+
      ((G k).edgeDensity S T : ℝ) = 1 := by
    exact_mod_cast offdiagonal_conservation G hG S T hdis hS hT i j k hij hik hjk
  linarith

end HadwigerRamsey.Main
