import HadwigerRamsey.ThomasonUpper.FiniteBlockTheorem

open scoped BigOperators Classical ENNReal
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- Appendix A.1, with exactly the manuscript's expression P and lower
bound on the number of parts. The class-index set is explicitly nonempty. -/
theorem multitype_complete_equipartition {n k s : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (ell : Fin k → ℕ) (hk : 0 < k)
    (hs : 2 ≤ s) (hell : ∀ i, 1 ≤ ell i)
    (hcard : ∀ i, (classVertices classes i).card = s*ell i)
    {tau omega phi : ℝ} (htau : 0 < tau) (htau1 : tau < 1)
    (homega : 1 ≤ omega) (hphi : 0 < phi) (hphi1 : phi < 1) :
    ∃ m : ℕ, ∃ U : Fin m → Finset (Fin n), 0 < m ∧ m ≤ s ∧
      (s : ℝ)-4*s/(omega*phi)-4*(s : ℝ)^2*
        ((2*omega)^(∑ i, ell i)*tau^(-((∑ i, (ell i : ℝ))*(k+phi*(∑ i, (ell i : ℝ)))))*
          (∏ i, ∏ j, (min 1 (1-blockDensity G classes i j+tau))^(ell i*ell j))) ≤ m ∧
      IsCompleteEquipartition G U := by
  let L := ∑ i, ell i
  have hL : 0 < L := by
    apply sum_pos'
    · intro i hi
      omega
    · exact ⟨⟨0,hk⟩,mem_univ _,by have := hell ⟨0,hk⟩; omega⟩
  obtain ⟨e,theta,htheta,hvertex,hshift,hlogmean⟩ := exists_sorted_nonneighbor_blocks
    G classes ell hs hell hcard hL rfl htau htau1.le
  let f := classBlockEnumeration classes ell e
  let flatTheta : (Σ i, Fin (ell i)) → ℝ := fun b => theta b.1 b.2
  let Q := ∏ i, ∏ j, (min 1 (1-blockDensity G classes i j+tau))^(ell i*ell j)
  have hQ : 0 < Q := by
    apply prod_pos
    intro i hi
    apply prod_pos
    intro j hj
    apply pow_pos
    exact lt_min (by norm_num) (by linarith [blockDensity_le_one G classes i j])
  have hI : Fintype.card (Σ i, Fin (ell i)) = L := by simp [L,Fintype.card_sigma]
  have hE : (eligibleBlocks ell).card+k = L := eligibleBlocks_card ell hell
  have hcountmean : ∀ position b, (𝔼 p : (Σ i, Fin (ell i)) → Equiv.Perm (Fin s),
      ((nonneighborIndices G f (fun i => p i position) b).card : ℝ)) ≤
        (s : ℝ)*(flatTheta b)^L := by
    intro position b
    let B := blockVertices f b
    have hrho : ∀ u ∈ B, nonneighborWeight G classes ell L tau u ≤ flatTheta b := by
      intro u hu
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
      exact hvertex b.1 b.2 x
    have hm := expected_block_nonneighbors G classes ell (by omega) hell hL rfl e hcard
      htau htau1.le position B hrho
    have heq : (𝔼 p : (Σ i, Fin (ell i)) → Equiv.Perm (Fin s),
        ((nonneighborIndices G f (fun i => p i position) b).card : ℝ)) =
        𝔼 p, (blockNonneighborCount G f position B p : ℝ) := by
      apply expect_congr rfl
      intro p hp
      exact congrArg (fun z : ℕ => (z : ℝ)) (nonneighborIndices_card_eq G f p position b)
    rw [heq]
    have hB : B.card = s := blockVertices_card f b
    simpa only [hB] using hm
  have hmax : ∀ M : Finset (Σ i, Fin (ell i)), M ⊆ eligibleBlocks ell →
      (∏ b ∈ M, (flatTheta b)^L) ≤ Q*tau^(-((L : ℝ)*((L : ℝ)-M.card))) := by
    intro M hME
    let D := fun i => univ.filter (fun a : Fin (ell i) => (⟨i,a⟩ : Σ i, Fin (ell i)) ∈ M)
    have hM : M = univ.sigma D := by
      ext b
      simp [D]
    have hcardM : (M.card : ℝ) = ∑ i, ((D i).card : ℝ) := by
      rw [hM,card_sigma,Nat.cast_sum]
    have heligible : ∀ i a, a ∈ D i → a.val+1 < ell i := by
      intro i a ha
      exact (mem_eligibleBlocks ell ⟨i,a⟩).mp (hME (mem_filter.mp ha).2)
    have hp := sorted_nonneighbor_max_product G classes ell hL rfl (by omega) e theta htau htau1.le
      (fun i a => (htheta i a).1) hshift hlogmean D heligible
    calc
      _ = ∏ i, ∏ a ∈ D i, (theta i a)^L := by rw [hM,prod_sigma]
      _ ≤ Q*tau^(-((L : ℝ)*((L : ℝ)-∑ i, ((D i).card : ℝ)))) := hp
      _ = _ := by rw [← hcardM]
  obtain ⟨m,U,hm,hms,hlower,hU⟩ := finite_block_equipartition G f hs hL hI flatTheta
    (eligibleBlocks ell) hE htau htau1.le homega hphi hQ
    (fun b => (htheta b.1 b.2).1) hcountmean hmax
  refine ⟨m,U,hm,hms,?_,hU⟩
  have hLR : (L : ℝ) = ∑ i, (ell i : ℝ) := by simp only [L,Nat.cast_sum]
  simpa only [Q,hLR] using hlower

end HadwigerRamsey.ThomasonUpper
