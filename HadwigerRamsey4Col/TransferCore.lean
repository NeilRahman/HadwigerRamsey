import HadwigerRamsey.ControlledPartition.Connectivity
import HadwigerRamsey.ControlledPartition.Interpretation

open Finset
open scoped Classical

namespace HadwigerRamsey4Col

open HadwigerRamsey.ControlledPartition

/-- The edges from a union of deleted vertices to the remaining graph
can be charged to the old boundary and to the new separator. -/
theorem boundary_delete_le {n : ℕ} (G : SimpleGraph (Fin n))
    (S A Z : Finset (Fin n)) (_hA : A ⊆ S)
    (hsep : ∀ u ∈ A, ∀ v ∈ S \ A, G.Adj u v → v ∈ Z) :
    (G.interedges (univ \ (S \ A)) (S \ A)).card ≤
      (G.interedges (univ \ S) S).card + A.card * Z.card := by
  classical
  have hsub : G.interedges (univ \ (S \ A)) (S \ A) ⊆
      G.interedges (univ \ S) S ∪ A ×ˢ Z := by
    intro e he
    obtain ⟨hu, hv, hadj⟩ := G.mem_interedges_iff.mp he
    by_cases huS : e.1 ∈ S
    · have huA : e.1 ∈ A := by
        by_contra h
        exact (mem_sdiff.mp hu).2 (mem_sdiff.mpr ⟨huS,h⟩)
      exact mem_union_right _ (mem_product.mpr ⟨huA,hsep _ huA _ hv hadj⟩)
    · exact mem_union_left _ (G.mem_interedges_iff.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _,huS⟩,(mem_sdiff.mp hv).1,hadj⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans_eq (by rw [card_product]))

/-- A quantitative finite core lemma. Every balanced cut has at least `b`
edges; a connectivity threshold `t` with `t*n < b` leaves a core occupying
more than `1-rho` of the vertices. -/
theorem exists_connected_core_of_cut_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 2 ≤ n) {rho t b : ℝ} (hrho : 0 < rho) (hrho4 : rho < 1/4)
    (ht : 0 ≤ t) (htn : t ≤ (n : ℝ)/4) (htb : t*n < b)
    (hcut : ∀ A : Finset (Fin n), rho*n ≤ (A.card : ℝ) →
      (A.card : ℝ) ≤ (1-rho)*n → b ≤ (G.interedges A (univ \ A)).card) :
    ∃ S : Finset (Fin n), (1-rho)*n < (S.card : ℝ) ∧ RealConnected G S t := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let good : Finset (Fin n) → Prop := fun S =>
    (1-rho)*n < (S.card : ℝ) ∧
    ((G.interedges (univ \ S) S).card : ℝ) ≤ t*((n : ℝ)-S.card)
  have hgood : good univ := by
    constructor
    · simp only [card_univ, Fintype.card_fin]
      nlinarith
    · simp
  obtain ⟨S,hS,hmin⟩ := (univ.filter good).exists_min_image Finset.card
    ⟨univ,mem_filter.mpr ⟨mem_univ _,hgood⟩⟩
  have hSgood := (mem_filter.mp hS).2
  refine ⟨S,hSgood.1,?_⟩
  by_contra hnot
  have hsize : t ≤ (S.card : ℝ)-1 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hs := hSgood.1
    nlinarith
  obtain ⟨Z,A,B,hZS,hZ,hAne,hBne,hdis,hunion,hno⟩ :=
    RealConnected.separator hsize hnot
  have hchoose : ∃ A : Finset (Fin n), A.Nonempty ∧ A ⊆ S ∧
      2*A.card ≤ n ∧ ∀ u ∈ A, ∀ v ∈ S \ A, G.Adj u v → v ∈ Z := by
    have hAB : A.card+B.card ≤ n := by
      rw [← card_union_of_disjoint hdis, hunion]
      exact (card_le_card sdiff_subset).trans (by simpa using S.card_le_univ)
    have haS : A ⊆ S := (subset_union_left.trans (by rw [hunion])).trans sdiff_subset
    have hbS : B ⊆ S := (subset_union_right.trans (by rw [hunion])).trans sdiff_subset
    by_cases hab : A.card ≤ B.card
    · refine ⟨A,hAne,haS,by omega,?_⟩
      intro u hu v hv huv
      by_contra hvZ
      have hvAB : v ∈ A ∪ B := by rw [hunion]; exact mem_sdiff.mpr ⟨(mem_sdiff.mp hv).1,hvZ⟩
      exact hno u hu v ((mem_union.mp hvAB).resolve_left (mem_sdiff.mp hv).2) huv
    · refine ⟨B,hBne,hbS,by omega,?_⟩
      intro u hu v hv huv
      by_contra hvZ
      have hvAB : v ∈ A ∪ B := by rw [hunion]; exact mem_sdiff.mpr ⟨(mem_sdiff.mp hv).1,hvZ⟩
      exact hno v ((mem_union.mp hvAB).resolve_right (mem_sdiff.mp hv).2) u hu (G.adj_symm huv)
  obtain ⟨A,hAne,hAS,hhalf,hsep⟩ := hchoose
  let T := S \ A
  let D := univ \ T
  have hcard : (T.card : ℝ) = (S.card : ℝ)-A.card := by
    dsimp only [T]
    rw [card_sdiff_of_subset hAS, Nat.cast_sub (card_le_card hAS)]
  have hDcard : (D.card : ℝ) = (n : ℝ)-T.card := by
    dsimp only [D]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      Nat.cast_sub (by simpa using T.card_le_univ)]
  have hboundary : ((G.interedges D T).card : ℝ) < t*D.card := by
    have hstep : ((G.interedges D T).card : ℝ) ≤
        (G.interedges (univ \ S) S).card + (A.card : ℝ)*Z.card := by
      exact_mod_cast boundary_delete_le G S A Z hAS hsep
    have haR : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
    have hzR := mul_lt_mul_of_pos_left hZ haR
    have hs := hSgood.2
    nlinarith
  have hDsmall : (D.card : ℝ) < rho*n := by
    by_contra h
    have hlow : rho*n ≤ (D.card : ℝ) := le_of_not_gt h
    have hhalfR : 2*(A.card : ℝ) ≤ n := by exact_mod_cast hhalf
    have hupp : (D.card : ℝ) ≤ (1-rho)*n := by
      have hs := hSgood.1
      nlinarith
    have hcomp : univ \ D = T := by ext v; simp [D]
    have hbound := hcut D hlow hupp
    rw [hcomp] at hbound
    have hDn : (D.card : ℝ) ≤ n := by exact_mod_cast (by simpa using D.card_le_univ : D.card ≤ n)
    have hmul := mul_le_mul_of_nonneg_left hDn ht
    linarith
  have hTgood : good T := by
    refine ⟨?_,?_⟩
    · nlinarith
    · change ((G.interedges D T).card : ℝ) ≤ t*((n : ℝ)-T.card)
      rw [← hDcard]
      exact hboundary.le
  have hminT := hmin T (mem_filter.mpr ⟨mem_univ _,hTgood⟩)
  have hlt : T.card < S.card := by
    dsimp only [T]
    rw [card_sdiff_of_subset hAS]
    have hpos := hAne.card_pos
    have hle := card_le_card hAS
    omega
  omega

/-- Lemma 6 of the component-transfer manuscript, with the exact strict
retained-order bound and the integer connectivity threshold. In fact order
at least two suffices. -/
theorem connected_core {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    {rho sigma : ℝ} (hrho : 0 < rho) (hrho4 : rho < 1/4) (hsigma : 0 < sigma)
    (hcut : ∀ A : Finset (Fin n), rho*n ≤ (A.card : ℝ) →
      (A.card : ℝ) ≤ (1-rho)*n →
      sigma*(n : ℝ)^2 ≤ (G.interedges A (univ \ A)).card) :
    ∃ S : Finset (Fin n), (1-rho)*n < (S.card : ℝ) ∧
      ⌊sigma*n/2⌋₊ ≤ HadwigerRamsey.ThomasonUpper.vertexConnectivity (inducedGraph G S) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨A,hA,hAc⟩ := exists_subset_card_eq (show n/2 ≤ (univ : Finset (Fin n)).card by simp; omega)
  have haN : 2*A.card ≤ n := by omega
  have haN' : n ≤ 2*A.card+1 := by omega
  have ha : 2*(A.card : ℝ) ≤ n := by exact_mod_cast haN
  have ha' : (n : ℝ) ≤ 2*(A.card : ℝ)+1 := by exact_mod_cast haN'
  have haLo : rho*n ≤ (A.card : ℝ) := by nlinarith
  have haHi : (A.card : ℝ) ≤ (1-rho)*n := by nlinarith
  have hc := hcut A haLo haHi
  have hAcmp : ((univ \ A).card : ℝ) = (n : ℝ)-A.card := by
    rw [card_sdiff_of_subset hA, card_univ, Fintype.card_fin,
      Nat.cast_sub (by simpa using A.card_le_univ)]
  have hprod : ((G.interedges A (univ \ A)).card : ℝ) ≤
      (A.card : ℝ)*((n : ℝ)-A.card) := by
    have hh := G.card_interedges_le_mul A (univ \ A)
    have hh' : ((G.interedges A (univ \ A)).card : ℝ) ≤
        (A.card : ℝ)*(univ \ A).card := by exact_mod_cast hh
    rwa [hAcmp] at hh'
  have hsigma4 : sigma ≤ 1/4 := by
    nlinarith [sq_nonneg ((A.card : ℝ)-(n : ℝ)/2),sq_pos_of_pos hnR]
  have hf : (⌊sigma*n/2⌋₊ : ℝ) ≤ sigma*n/2 := Nat.floor_le (by positivity)
  obtain ⟨S,hS,hconn⟩ := exists_connected_core_of_cut_bound G hn hrho hrho4
    (t := (⌊sigma*n/2⌋₊ : ℝ)) (b := sigma*(n : ℝ)^2)
    (by positivity) (by nlinarith) (by nlinarith [sq_pos_of_pos hnR]) hcut
  have hSne : S.Nonempty := card_pos.mp (by
    have hspos : (0 : ℝ) < S.card := by nlinarith
    exact_mod_cast hspos)
  refine ⟨S,hS,?_⟩
  exact_mod_cast (realConnected_iff_vertexConnectivity G S hSne _).mp hconn

/-- Lemma 6, with the manuscript's sufficiently-large-order quantifiers.
The stronger finite result above permits the uniform cutoff `N₀ = 2`. -/
theorem lemma6 (rho sigma : ℝ) (hrho : 0 < rho) (hrho4 : rho < 1/4)
    (hsigma : 0 < sigma) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H : SimpleGraph (Fin N),
      (∀ A : Finset (Fin N), rho*N ≤ (A.card : ℝ) →
        (A.card : ℝ) ≤ (1-rho)*N →
        sigma*(N : ℝ)^2 ≤ (H.interedges A (univ \ A)).card) →
      ∃ S : Finset (Fin N), (1-rho)*N < (S.card : ℝ) ∧
        ⌊sigma*N/2⌋₊ ≤
          HadwigerRamsey.ThomasonUpper.vertexConnectivity (inducedGraph H S) := by
  exact ⟨2, fun N hN H hcut => connected_core H hN hrho hrho4 hsigma hcut⟩

end HadwigerRamsey4Col
