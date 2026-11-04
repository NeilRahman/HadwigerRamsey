import HadwigerRamsey.Main.Trimming
import HadwigerRamsey.DenseMinor
import HadwigerRamsey.TwoBigSets.Minor
import HadwigerRamsey.ControlledPartition.Interpretation
import HadwigerRamsey.ThomasonUpper.Restriction

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.Main

attribute [-instance] SimpleGraph.instDecidableComapAdj in
theorem internal_minor {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) {K γ : ℝ} {N : ℕ} (hN : N ≤ A.card) (ha : 2 ≤ A.card)
    (hdense : ∀ m ≥ N, ∀ H : SimpleGraph (Fin m),
      (1-γ)*(m.choose 2 : ℝ) ≤ H.edgeFinset.card →
      K*m/sqrt (log (m : ℝ)) ≤ (hadwigerNumber H : ℝ))
    (hdensity : 1-γ ≤ internalDensity G A) :
    K*A.card/sqrt (log (A.card : ℝ)) ≤ (hadwigerNumber G : ℝ) := by
  classical
  let f : Fin A.card → Fin n := fun i => (A.equivFin.symm i).val
  have hf : Function.Injective f := by
    intro i j hij
    exact A.equivFin.symm.injective (Subtype.ext hij)
  have him : (univ : Finset (Fin A.card)).image f = A := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact (A.equivFin.symm i).property
    · intro hv
      exact mem_image.mpr ⟨A.equivFin ⟨v,hv⟩,mem_univ _,by simp [f]⟩
  let H := G.comap f
  have hdH : internalDensity H univ = internalDensity G A := by
    change internalDensity (G.comap f) univ = _
    rw [internalDensity_comap G f hf,him]
  let e : H.induce (↑(univ : Finset (Fin A.card)) : Set (Fin A.card)) ≃g H :=
    { toEquiv := Equiv.ofBijective (fun v => v.val)
        ⟨Subtype.val_injective, fun v => ⟨⟨v,mem_univ _⟩,rfl⟩⟩
      map_rel_iff' := by intro v w; rfl }
  have hU := e.card_edgeFinset_eq
  have hratio : internalDensity H univ =
      (H.edgeFinset.card : ℝ)/(A.card.choose 2 : ℝ) := by
    unfold internalDensity
    simpa only [card_univ,Fintype.card_fin,← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card,Nat.card_fin] using
      congrArg (fun c : ℕ => (c : ℝ)/(A.card.choose 2 : ℝ)) hU
  have hden : (0 : ℝ) < A.card.choose 2 := by exact_mod_cast Nat.choose_pos ha
  have he : (1-γ)*(A.card.choose 2 : ℝ) ≤ H.edgeFinset.card := by
    have hd' : 1-γ ≤ (H.edgeFinset.card : ℝ)/(A.card.choose 2 : ℝ) := by
      rw [←hratio,hdH]
      exact hdensity
    exact (le_div_iff₀ hden).mp hd'
  have hm := hdense A.card hN H he
  exact hm.trans (by exact_mod_cast hadwigerNumber_comap_le G f hf)

theorem cross_minor_unequal {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hdis : Disjoint A B) {K γ : ℝ} {N : ℕ}
    (hA : 0 < A.card) (hB : 0 < B.card) (hN : N ≤ min A.card B.card)
    (hbip : ∀ m : ℕ, ∀ H : SimpleGraph (Fin m), ∀ X Y : Finset (Fin m),
      H.IsBipartiteWith (X : Set (Fin m)) (Y : Set (Fin m)) →
      X ∪ Y = univ → X.card = Y.card → N ≤ X.card →
      (1-γ)*(X.card : ℝ)^2 ≤ H.edgeFinset.card →
      K*(X.card : ℝ)/sqrt (log (X.card : ℝ)) ≤ (hadwigerNumber H : ℝ))
    (hdensity : 1-γ ≤ (G.edgeDensity A B : ℝ)) :
    K*((min A.card B.card : ℕ) : ℝ)/sqrt (log ((min A.card B.card : ℕ) : ℝ)) ≤
      (hadwigerNumber G : ℝ) := by
  classical
  have hden : (0 : ℝ) < (A.card : ℝ)*B.card := by positivity
  have hed : (1-γ)*(A.card : ℝ)*B.card ≤ (G.interedges A B).card := by
    have he : (G.edgeDensity A B : ℝ) =
        ((G.interedges A B).card : ℝ)/((A.card : ℝ)*B.card) := by
      simp only [SimpleGraph.edgeDensity_def,Rat.cast_div,Rat.cast_natCast,Rat.cast_mul]
    rw [he] at hdensity
    nlinarith only [(le_div_iff₀ hden).mp hdensity]
  obtain ⟨A',hA',B',hB',hcA,hcB,hd⟩ := balanced_dense_subsets G A B hA hB hed
  have hm := TwoBigSets.cross_minor G A' B' (hdis.mono hA' hB')
    (hcA.trans hcB.symm) (by simpa only [hcA] using hN) hbip hd
  simpa only [hcA] using hm

theorem scale_minor_bound {n a : ℕ} {b K : ℝ} (hK : 0 ≤ K)
    (ha : 2 ≤ a) (han : a ≤ n) (hsize : b*n ≤ (a : ℝ)) :
    K*b*n/sqrt (log (n : ℝ)) ≤ K*a/sqrt (log (a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hroot : 0 < sqrt (log (a : ℝ)) :=
    sqrt_pos.mpr (log_pos (by exact_mod_cast (by omega : 1 < a)))
  have hrootle : sqrt (log (a : ℝ)) ≤ sqrt (log (n : ℝ)) :=
    sqrt_le_sqrt (log_le_log haR (by exact_mod_cast han))
  calc
    _ ≤ K*a/sqrt (log (n : ℝ)) := div_le_div_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_left hsize hK]) (sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hroot hrootle

theorem internal_density_cap {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) {K γ b : ℝ} {N : ℕ} (hK : 0 ≤ K)
    (hN : N ≤ A.card) (ha : 2 ≤ A.card) (hsize : b*n ≤ (A.card : ℝ))
    (hdense : ∀ m ≥ N, ∀ H : SimpleGraph (Fin m),
      (1-γ)*(m.choose 2 : ℝ) ≤ H.edgeFinset.card →
      K*m/sqrt (log (m : ℝ)) ≤ (hadwigerNumber H : ℝ))
    (hsmall : (hadwigerNumber G : ℝ) < K*b*n/sqrt (log (n : ℝ))) :
    internalDensity G A < 1-γ := by
  by_contra! hd
  have hm := internal_minor G A hN ha hdense hd
  have hs := scale_minor_bound hK ha (by simpa using A.card_le_univ : A.card ≤ n) hsize
  exact (not_lt_of_ge (hs.trans hm)) hsmall

theorem cross_density_cap {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hdis : Disjoint A B) {K γ b : ℝ} {N : ℕ}
    (hK : 0 ≤ K) (hN : N ≤ min A.card B.card)
    (ha : 2 ≤ min A.card B.card) (hsize : b*n ≤ ((min A.card B.card : ℕ) : ℝ))
    (hbip : ∀ m : ℕ, ∀ H : SimpleGraph (Fin m), ∀ X Y : Finset (Fin m),
      H.IsBipartiteWith (X : Set (Fin m)) (Y : Set (Fin m)) →
      X ∪ Y = univ → X.card = Y.card → N ≤ X.card →
      (1-γ)*(X.card : ℝ)^2 ≤ H.edgeFinset.card →
      K*(X.card : ℝ)/sqrt (log (X.card : ℝ)) ≤ (hadwigerNumber H : ℝ))
    (hsmall : (hadwigerNumber G : ℝ) < K*b*n/sqrt (log (n : ℝ))) :
    (G.edgeDensity A B : ℝ) < 1-γ := by
  by_contra! hd
  have hm := cross_minor_unequal G A B hdis (by omega) (by omega) hN hbip hd
  have han : min A.card B.card ≤ n := (min_le_left _ _).trans (by simpa using A.card_le_univ)
  exact (not_lt_of_ge ((scale_minor_bound hK ha han hsize).trans hm)) hsmall

end HadwigerRamsey.Main
