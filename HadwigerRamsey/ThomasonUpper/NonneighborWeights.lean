import HadwigerRamsey.ThomasonUpper.DensityDeletion

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- Diagonal complementary densities use the same unordered-pair
normalization as the original graph. -/
theorem internalDensity_add_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : 2 ≤ S.card) :
    internalDensity G S + internalDensity Gᶜ S = 1 := by
  classical
  obtain ⟨u,hu,v,hv,huv⟩ := one_lt_card.mp (by omega : 1 < S.card)
  have hOff : S.offDiag.Nonempty := ⟨(u,v),mem_offDiag.mpr ⟨hu,hv,huv⟩⟩
  let R := fun (e : V × V) (_ : Unit) => G.Adj e.1 e.2
  have he : Rel.interedges (fun (e : V × V) (_ : Unit) => Gᶜ.Adj e.1 e.2) S.offDiag {()} =
      Rel.interedges (fun e x => ¬R e x) S.offDiag {()} := by
    ext ⟨⟨x,y⟩,z⟩
    simp only [Rel.mem_interedges_iff,mem_offDiag,SimpleGraph.compl_adj,R]
    tauto
  have hd : Rel.edgeDensity (fun (e : V × V) (_ : Unit) => Gᶜ.Adj e.1 e.2) S.offDiag {()} =
      Rel.edgeDensity (fun e x => ¬R e x) S.offDiag {()} := by
    unfold Rel.edgeDensity
    rw [he]
  have hh := Rel.edgeDensity_add_edgeDensity_compl R hOff (singleton_nonempty ())
  rw [internalDensity_eq_offDiag_density,internalDensity_eq_offDiag_density]
  have hhR : (Rel.edgeDensity R S.offDiag {()} : ℝ) +
      (Rel.edgeDensity (fun e x => ¬R e x) S.offDiag {()} : ℝ) = 1 := by exact_mod_cast hh
  exact (congrArg (fun q : ℚ => (Rel.edgeDensity R S.offDiag {()} : ℝ)+(q : ℝ)) hd).trans hhR

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- Summing the neighbor counts into T counts every ordered interedge once. -/
theorem sum_neighbor_counts {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S T : Finset V) :
    (∑ u ∈ S, (T.filter (G.Adj u)).card) = (G.interedges S T).card := by
  classical
  rw [SimpleGraph.interedges,Rel.interedges_eq_biUnion,card_biUnion]
  · simp only [card_map]
  · intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,_,hx⟩ := mem_map.mp he
    obtain ⟨y,_,hy⟩ := mem_map.mp hf
    exact huv (congrArg Prod.fst (hx.trans hy.symm))

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The nonneighbor fraction d_j(u) used in appendix A.1. The complement
graph automatically excludes u itself, exactly as the manuscript does. -/
noncomputable def nonneighborFraction {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (j : Fin k) (u : Fin n) : ℝ :=
  (((classVertices τ j).filter (Gᶜ.Adj u)).card : ℝ)/(classVertices τ j).card

attribute [-instance] SimpleGraph.Compl.adjDecidable in
theorem average_nonneighborFraction {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) :
    (∑ u ∈ classVertices τ i, nonneighborFraction G τ j u)/(classVertices τ i).card =
      (Gᶜ.edgeDensity (classVertices τ i) (classVertices τ j) : ℝ) := by
  simp only [nonneighborFraction,← sum_div,← Nat.cast_sum,
    SimpleGraph.edgeDensity_def,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]
  have hh := sum_neighbor_counts Gᶜ (classVertices τ i) (classVertices τ j)
  calc
    _ = ((Gᶜ.interedges (classVertices τ i) (classVertices τ j)).card : ℝ)/
        (classVertices τ j).card/(classVertices τ i).card :=
      congrArg (fun c : ℕ => (c : ℝ)/(classVertices τ j).card/(classVertices τ i).card) hh
    _ = _ := by ring

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The average nonneighbor fraction is at most the complementary block
density, including the diagonal normalization correction. -/
theorem average_nonneighborFraction_le {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) (hs : ∀ i, 2 ≤ (classVertices τ i).card) :
    (∑ u ∈ classVertices τ i, nonneighborFraction G τ j u)/(classVertices τ i).card ≤
      1-blockDensity G τ i j := by
  classical
  rw [average_nonneighborFraction]
  by_cases hij : i = j
  · subst j
    have hh := internalDensity_add_compl G (classVertices τ i) (hs i)
    have hl := edgeDensity_le_internalDensity Gᶜ (classVertices τ i) (hs i)
    simp only [blockDensity,eq_self_iff_true,ite_true]
    exact hl.trans_eq (eq_sub_of_add_eq' hh)
  · have hdisj : Disjoint (classVertices τ i) (classVertices τ j) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact hij (((mem_filter.mp hx).2).symm.trans (mem_filter.mp hy).2)
    have hi : (classVertices τ i).Nonempty := card_pos.mp (by have := hs i; omega)
    have hj : (classVertices τ j).Nonempty := card_pos.mp (by have := hs j; omega)
    have hh := G.edgeDensity_add_edgeDensity_compl hi hj hdisj
    have hhR : (G.edgeDensity (classVertices τ i) (classVertices τ j) : ℝ) +
        Gᶜ.edgeDensity (classVertices τ i) (classVertices τ j) = 1 := by
      have hc : (SimpleGraph.Compl.adjDecidable (Fin n) G) = (Classical.decRel Gᶜ.Adj) := Subsingleton.elim _ _
      have he := congrArg (fun d : DecidableRel Gᶜ.Adj =>
        @SimpleGraph.edgeDensity (Fin n) Gᶜ d (classVertices τ i) (classVertices τ j)) hc
      calc
        _ = (G.edgeDensity (classVertices τ i) (classVertices τ j) : ℝ) +
            (@SimpleGraph.edgeDensity (Fin n) Gᶜ (SimpleGraph.Compl.adjDecidable (Fin n) G)
              (classVertices τ i) (classVertices τ j) : ℝ) :=
          congrArg (fun q : ℚ => (G.edgeDensity (classVertices τ i) (classVertices τ j) : ℝ)+(q : ℝ)) he.symm
        _ = 1 := by exact_mod_cast hh
    simp only [blockDensity,if_neg hij]
    linarith

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- Regularizing the nonneighbor fractions preserves the corresponding
regularized complementary-density upper bound on their class average. -/
theorem average_regularized_nonneighbor_le {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) (hs : ∀ i, 2 ≤ (classVertices τ i).card)
    (t : ℝ) :
    (∑ u ∈ classVertices τ i, min 1 (nonneighborFraction G τ j u+t))/(classVertices τ i).card ≤
      min 1 (1-blockDensity G τ i j+t) := by
  have hcard : (0 : ℝ) < (classVertices τ i).card := by
    exact_mod_cast (by have := hs i; omega : 0 < (classVertices τ i).card)
  apply le_min
  · apply (div_le_iff₀ hcard).mpr
    have hh := sum_le_sum (fun u (_ : u ∈ classVertices τ i) =>
      min_le_left (1:ℝ) (nonneighborFraction G τ j u+t))
    simpa only [one_mul,sum_const,nsmul_eq_mul,mul_one] using hh
  · have hh := sum_le_sum (fun u (_ : u ∈ classVertices τ i) =>
      min_le_right (1:ℝ) (nonneighborFraction G τ j u+t))
    have hb := average_nonneighborFraction_le G τ i j hs
    have he : (∑ u ∈ classVertices τ i, (nonneighborFraction G τ j u+t)) =
        (∑ u ∈ classVertices τ i, nonneighborFraction G τ j u)+(classVertices τ i).card*t := by
      simp only [sum_add_distrib,sum_const,nsmul_eq_mul]
    rw [he] at hh
    apply (div_le_iff₀ hcard).mpr
    have hb' := (div_le_iff₀ hcard).mp hb
    nlinarith

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The logarithmic form of AM-GM, using Mathlib's log x <= x-1.
It avoids taking roots while preserving the manuscript's geometric mean. -/
theorem sum_log_le_card_mul_log {V : Type*} (S : Finset V) (z : V → ℝ) {q : ℝ}
    (hz : ∀ u ∈ S, 0 < z u) (hq : 0 < q)
    (hsum : (∑ u ∈ S, z u) ≤ S.card*q) :
    (∑ u ∈ S, log (z u)) ≤ S.card*log q := by
  have ht : ∀ u ∈ S, log (z u)-log q ≤ z u/q-1 := by
    intro u hu
    have hh := log_le_sub_one_of_pos (div_pos (hz u hu) hq)
    rwa [log_div (hz u hu).ne' hq.ne'] at hh
  have hh := sum_le_sum ht
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,← sum_div] at hh
  have hd : (∑ u ∈ S, z u)/q ≤ S.card := (div_le_iff₀ hq).mpr hsum
  linarith

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The regularized nonneighbor logarithms satisfy the class-average
inequality from A.1, including the diagonal case. -/
theorem average_log_regularized_nonneighbor_le {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) (hs : ∀ i, 2 ≤ (classVertices τ i).card)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∑ u ∈ classVertices τ i, log (min 1 (nonneighborFraction G τ j u+t)))/
      (classVertices τ i).card ≤ log (min 1 (1-blockDensity G τ i j+t)) := by
  have hcard : (0 : ℝ) < (classVertices τ i).card := by
    exact_mod_cast (by have := hs i; omega : 0 < (classVertices τ i).card)
  have hp : ∀ u, 0 < min 1 (nonneighborFraction G τ j u+t) := by
    intro u
    have hh : 0 ≤ nonneighborFraction G τ j u := by unfold nonneighborFraction; positivity
    exact lt_min (by norm_num) (by linarith)
  have hq : 0 < min 1 (1-blockDensity G τ i j+t) :=
    lt_min (by norm_num) (by linarith [blockDensity_le_one G τ i j])
  have ha := average_regularized_nonneighbor_le G τ i j hs t
  have hb := sum_log_le_card_mul_log (classVertices τ i)
    (fun u => min 1 (nonneighborFraction G τ j u+t)) (fun u _ => hp u) hq
    (by nlinarith [(div_le_iff₀ hcard).mp ha])
  apply (div_le_iff₀ hcard).mpr
  nlinarith

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The logarithm of the manuscript's rho geometric-mean estimate.
The product is over all class indices, with the original ell_j/ell weights. -/
theorem rho_geomean_log_bound {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i : Fin k) (hs : ∀ i, 2 ≤ (classVertices τ i).card)
    (ell : Fin k → ℕ) (L : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∑ u ∈ classVertices τ i, log (∏ j, (min 1 (nonneighborFraction G τ j u+t))^
      ((ell j : ℝ)/L)))/(classVertices τ i).card ≤
      ∑ j, ((ell j : ℝ)/L)*log (min 1 (1-blockDensity G τ i j+t)) := by
  have hp : ∀ u j, 0 < min 1 (nonneighborFraction G τ j u+t) := by
    intro u j
    have hh : 0 ≤ nonneighborFraction G τ j u := by unfold nonneighborFraction; positivity
    exact lt_min (by norm_num) (by linarith)
  have hlog : ∀ u, log (∏ j, (min 1 (nonneighborFraction G τ j u+t))^((ell j : ℝ)/L)) =
      ∑ j, ((ell j : ℝ)/L)*log (min 1 (nonneighborFraction G τ j u+t)) := by
    intro u
    rw [log_prod (fun j _ => (rpow_pos_of_pos (hp u j) _).ne')]
    apply sum_congr rfl
    intro j _
    exact log_rpow (hp u j) _
  simp_rw [hlog]
  rw [sum_comm,Finset.sum_div]
  apply sum_le_sum
  intro j _
  rw [← mul_sum,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (average_log_regularized_nonneighbor_le G τ i j hs ht ht1) (by positivity)

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- Equation rho-geomean from appendix A.1, in its original product and
geometric-mean form. The random-partition argument is a separate step. -/
theorem rho_geomean_bound {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i : Fin k) (hs : ∀ i, 2 ≤ (classVertices τ i).card)
    (ell : Fin k → ℕ) (L : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∏ u ∈ classVertices τ i, ∏ j, (min 1 (nonneighborFraction G τ j u+t))^
      ((ell j : ℝ)/L))^(1/((classVertices τ i).card : ℝ)) ≤
      ∏ j, (min 1 (1-blockDensity G τ i j+t))^((ell j : ℝ)/L) := by
  let rho := fun u => ∏ j, (min 1 (nonneighborFraction G τ j u+t))^((ell j : ℝ)/L)
  let q := fun j => min 1 (1-blockDensity G τ i j+t)
  have hp : ∀ u j, 0 < min 1 (nonneighborFraction G τ j u+t) := by
    intro u j
    have hh : 0 ≤ nonneighborFraction G τ j u := by unfold nonneighborFraction; positivity
    exact lt_min (by norm_num) (by linarith)
  have hrho : ∀ u, 0 < rho u := fun u => prod_pos (fun j _ => rpow_pos_of_pos (hp u j) _)
  have hq : ∀ j, 0 < q j := fun j => lt_min (by norm_num)
    (by linarith [blockDensity_le_one G τ i j])
  have hprod : 0 < ∏ u ∈ classVertices τ i, rho u := prod_pos (fun u _ => hrho u)
  have hl : log ((∏ u ∈ classVertices τ i, rho u)^(1/((classVertices τ i).card : ℝ))) =
      (∑ u ∈ classVertices τ i, log (rho u))/(classVertices τ i).card := by
    rw [log_rpow hprod,log_prod (fun u _ => (hrho u).ne')]
    ring
  have hr : log (∏ j, (q j)^((ell j : ℝ)/L)) = ∑ j, ((ell j : ℝ)/L)*log (q j) := by
    rw [log_prod (fun j _ => (rpow_pos_of_pos (hq j) _).ne')]
    apply sum_congr rfl
    intro j _
    exact log_rpow (hq j) _
  apply (log_le_log_iff (rpow_pos_of_pos hprod _) (prod_pos (fun j _ => rpow_pos_of_pos (hq j) _))).mp
  rw [hl,hr]
  exact rho_geomean_log_bound G τ i hs ell L ht ht1

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The range tau <= rho(u) <= 1 from A.1, with the prescribed integer
class counts summing to ell. -/
theorem rho_bounds {n k : ℕ} (G : SimpleGraph (Fin n)) (τ : Fin n → Fin k)
    (ell : Fin k → ℕ) (L : ℕ) (hL : 0 < L) (hsum : ∑ j, ell j = L)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (u : Fin n) :
    t ≤ ∏ j, (min 1 (nonneighborFraction G τ j u+t))^((ell j : ℝ)/L) ∧
      (∏ j, (min 1 (nonneighborFraction G τ j u+t))^((ell j : ℝ)/L)) ≤ 1 := by
  have hsumR : ∑ j, ((ell j : ℝ)/L) = 1 := by
    rw [← sum_div,← Nat.cast_sum,hsum,div_self (by exact_mod_cast hL.ne')]
  have hb : ∀ j, t ≤ min 1 (nonneighborFraction G τ j u+t) := by
    intro j
    have hh : 0 ≤ nonneighborFraction G τ j u := by unfold nonneighborFraction; positivity
    exact le_min ht1 (by linarith)
  constructor
  · calc
      t = ∏ j, t^((ell j : ℝ)/L) := by rw [← rpow_sum_of_pos ht,hsumR,rpow_one]
      _ ≤ _ := prod_le_prod (fun j _ => rpow_nonneg ht.le _) (fun j _ =>
        rpow_le_rpow ht.le (hb j) (by positivity))
  · calc
      _ ≤ ∏ _j : Fin k, (1 : ℝ) := prod_le_prod
        (fun j _ => rpow_nonneg (ht.le.trans (hb j)) _) (fun j _ => by
          simpa only [one_rpow] using rpow_le_rpow (ht.le.trans (hb j))
            (min_le_left (1:ℝ) (nonneighborFraction G τ j u+t)) (by positivity : 0 ≤ (ell j : ℝ)/L))
      _ = 1 := by simp

end HadwigerRamsey.ThomasonUpper
