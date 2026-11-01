import HadwigerRamsey.ThomasonUpper.BlockNonneighbors
import HadwigerRamsey.ThomasonUpper.ConditionalBlocks
import HadwigerRamsey.ThomasonUpper.RandomEquipartition
import HadwigerRamsey.ThomasonUpper.SelectedBlocks

open scoped BigOperators Classical ENNReal
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- Rejection is a property of the first transversal, independent of
which position of the random ordering produced it. -/
def blockRejection {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (e : I × Fin s ≃ V) (theta : I → ℝ) (L : ℕ)
    (omega : ℝ) (b : I) : Set (I → Fin s) :=
  {x | omega*(s : ℝ)*(theta b)^L < (nonneighborIndices G e x b).card}

def acceptableVectors {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (e : I × Fin s ≃ V) (theta : I → ℝ) (E : Finset I)
    (L : ℕ) (omega phi : ℝ) : Set (I → Fin s) :=
  {x | ((occurringEvents E (blockRejection G e theta L omega) x).card : ℝ) ≤ phi*L}

/-- A.1 from its sorted-block product and expected-block-count estimates.
All sampling, conditioning, rejection, defect deletion, and redistribution
are proved here; the two input estimates are supplied by the graph lemmas. -/
theorem finite_block_equipartition {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    [DecidableEq V] {s L k : ℕ} (G : SimpleGraph V) (e : I × Fin s ≃ V)
    (hs : 2 ≤ s) (hL : 0 < L) (hI : Fintype.card I = L)
    (theta : I → ℝ) (E : Finset I) (hE : E.card+k = L)
    {tau omega phi Q : ℝ} (htau : 0 < tau) (htau1 : tau ≤ 1)
    (homega : 1 ≤ omega) (hphi : 0 < phi) (hQ : 0 < Q)
    (htheta : ∀ b, tau ≤ theta b)
    (hmean : ∀ t b, (𝔼 p : I → Equiv.Perm (Fin s),
      ((nonneighborIndices G e (fun i => p i t) b).card : ℝ)) ≤ (s : ℝ)*(theta b)^L)
    (hmax : ∀ M : Finset I, M ⊆ E →
      (∏ b ∈ M, (theta b)^L) ≤ Q*tau^(-((L : ℝ)*((L : ℝ)-M.card)))) :
    ∃ m : ℕ, ∃ U : Fin m → Finset V, 0 < m ∧ m ≤ s ∧
      (s : ℝ)-4*s/(omega*phi)-4*(s : ℝ)^2*
        ((2*omega)^L*tau^(-((L : ℝ)*(k+phi*L)))*Q) ≤ m ∧
      IsCompleteEquipartition G U := by
  let P := (2*omega)^L*tau^(-((L : ℝ)*(k+phi*L)))*Q
  let R := blockRejection G e theta L omega
  let C := acceptableVectors G e theta E L omega phi
  let ok : Fin s → Set (I → Equiv.Perm (Fin s)) :=
    fun t => {p | (fun i => p i t) ∈ C}
  have hspos : 0 < s := by omega
  have hsR : (1 : ℝ) < s := by exact_mod_cast (by omega : 1 < s)
  have homega0 : 0 < omega := by linarith
  have hPpos : 0 < P := mul_pos (mul_pos (pow_pos (by linarith) _)
    (rpow_pos_of_pos htau _)) hQ
  have hEcard : E.card ≤ L := by omega
  have hbad : ∀ t, ((PMF.uniformOfFintype (I → Equiv.Perm (Fin s))).toOuterMeasure (ok t)ᶜ).toReal ≤
      1/(omega*phi) := by
    intro t
    let events := fun b => {p : I → Equiv.Perm (Fin s) | (fun i => p i t) ∈ R b}
    have hrej : ∀ b ∈ E,
        ((PMF.uniformOfFintype (I → Equiv.Perm (Fin s))).toOuterMeasure (events b)).toReal ≤ 1/omega := by
      intro b hb
      have hpos : 0 < (s : ℝ)*(theta b)^L :=
        mul_pos (by exact_mod_cast hspos) (pow_pos (htau.trans_le (htheta b)) _)
      have hevent : events b =
          {p | omega*((s : ℝ)*(theta b)^L) < ((nonneighborIndices G e (fun i => p i t) b).card : ℝ)} := by
        ext p
        simp only [events,R,blockRejection,Set.mem_ofPred_eq,mul_assoc]
      rw [hevent]
      exact rejected_block_probability
        (fun p : I → Equiv.Perm (Fin s) => ((nonneighborIndices G e (fun i => p i t) b).card : ℝ))
        (fun _ => by positivity) hpos homega0 (hmean t b)
    have he : (ok t)ᶜ =
        {p | phi*(L : ℝ) < ((E.filter (fun b => p ∈ events b)).card : ℝ)} := by
      ext p
      have hcount : E.filter (fun b => p ∈ events b) = occurringEvents E R (fun i => p i t) := by
        ext b
        simp only [occurringEvents,mem_filter,events,Set.mem_ofPred_eq]
      simp only [ok,C,acceptableVectors,Set.mem_compl_iff,Set.mem_ofPred_eq,not_le]
      rw [hcount]
    rw [he]
    exact unacceptable_probability E events homega0 hphi hL hEcard hrej
  have hproduct : ∀ x : I → Fin s, x ∈ C →
      (∏ b, ((nonneighborIndices G e x b).card : ℝ)/((s : ℝ)-1)) ≤ P := by
    intro x hx
    let D := occurringEvents E R x
    let M := E \ D
    have hDE : D ⊆ E := filter_subset _ _
    have hME : M ⊆ E := sdiff_subset
    have hsplit : M.card+D.card = E.card := card_sdiff_add_card_eq_card hDE
    have hmissing : (L : ℝ)-M.card ≤ k+phi*L := by
      have heR : (E.card : ℝ)+k = L := by exact_mod_cast hE
      have hsR : (M.card : ℝ)+D.card = E.card := by exact_mod_cast hsplit
      change (D.card : ℝ) ≤ phi*L at hx
      linarith
    have hper : ∀ b, 0 ≤ ((nonneighborIndices G e x b).card : ℝ)/((s : ℝ)-1) ∧
        ((nonneighborIndices G e x b).card : ℝ)/((s : ℝ)-1) ≤ 1 := by
      intro b
      constructor
      · positivity
      · have hsubset : nonneighborIndices G e x b ⊆ univ.erase (x b) := by
          intro y hy
          exact mem_erase.mpr ⟨fun h => nonneighborIndices_exclude G e x b (h ▸ hy),mem_univ _⟩
        have hc := card_le_card hsubset
        rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at hc
        apply (div_le_iff₀ (by linarith : 0 < (s : ℝ)-1)).mpr
        have hcR : ((nonneighborIndices G e x b).card : ℝ) ≤ (s : ℝ)-1 := by
          have hh : ((nonneighborIndices G e x b).card : ℝ) ≤ ((s-1 : ℕ) : ℝ) := by exact_mod_cast hc
          rw [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one] at hh
          exact hh
        linarith
    have hselected : ∀ b ∈ M,
        ((nonneighborIndices G e x b).card : ℝ)/((s : ℝ)-1) ≤
          omega*(s : ℝ)*(theta b)^L/((s : ℝ)-1) := by
      intro b hb
      have hnot : ¬omega*(s : ℝ)*(theta b)^L < (nonneighborIndices G e x b).card := by
        intro h
        exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨(mem_sdiff.mp hb).1,h⟩)
      exact div_le_div_of_nonneg_right (le_of_not_gt hnot) (by linarith)
    exact acceptable_pair_product_bound M
      (fun b => ((nonneighborIndices G e x b).card : ℝ)/((s : ℝ)-1)) theta hs homega htau htau1 hQ.le
      ((card_le_card hME).trans hEcard) hper
      (fun b _ => htau.le.trans (htheta b)) hselected (hmax M hME) hmissing
  have hpair : ∀ t u, t ≠ u →
      ((PMF.uniformOfFintype (I → Equiv.Perm (Fin s))).toOuterMeasure
        {p | p ∈ ok t ∧ p ∈ ok u ∧ ¬PartsJoined G (blockPart e p t) (blockPart e p u)}).toReal ≤ P := by
    intro t u htu
    have hsub : {p : I → Equiv.Perm (Fin s) |
        p ∈ ok t ∧ p ∈ ok u ∧ ¬PartsJoined G (blockPart e p t) (blockPart e p u)} ⊆
        {p | (fun i => p i t) ∈ C ∧ ∀ b, p b u ∈ nonneighborIndices G e (fun i => p i t) b} := by
      intro p hp
      exact ⟨hp.1,no_edge_second_part_indices G e p t u htu hp.2.2⟩
    exact (uniform_probability_mono hsub).trans
      (acceptable_second_part_probability hspos t u htu (fun x => x ∈ C)
        (nonneighborIndices G e) hPpos.le (nonneighborIndices_exclude G e) hproduct)
  obtain ⟨m,U,hm,hms,hlower,hU⟩ := complete_equipartition_of_probability_bounds G hspos hL
    (blockPart e) (fun p i => (blockPart_card e p i).trans hI)
    (fun p _ _ h => blockPart_disjoint e p h) ok
    (one_div_pos.mpr (mul_pos homega0 hphi)) hPpos hbad hpair
  refine ⟨m,U,hm,hms,?_,hU⟩
  convert hlower using 1 <;> simp only [P] <;> ring

end HadwigerRamsey.ThomasonUpper
