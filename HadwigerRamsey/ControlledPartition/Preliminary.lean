import HadwigerRamsey.ControlledPartition.Basic
import HadwigerRamsey.ControlledPartition.Decomposition
import HadwigerRamsey.ControlledPartition.Connectivity

open Finset
open scoped Classical BigOperators

namespace HadwigerRamsey.ControlledPartition

/-- A maximum-order induced subgraph with prescribed minimum degree leaves a
remainder of bounded degeneracy. The selected subgraph may be empty. -/
theorem exists_degree_core {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) :
    ∃ H : Finset (Fin n),
      (∀ v ∈ H, d ≤ ((nbr G H v).card : ℝ)) ∧
      DegenerateOn G (univ \ H) d := by
  classical
  let C : Set (Finset (Fin n)) := {S | ∀ v ∈ S, d ≤ ((nbr G S v).card : ℝ)}
  have hc : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨H,hH,hmax⟩ := C.exists_max_image Finset.card (Set.toFinite C) hc
  refine ⟨H,hH,?_⟩
  intro S hS hSne
  by_contra! hbad
  have hU : H ∪ S ∈ C := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact (hH v hv).trans (by
        exact_mod_cast card_le_card (show nbr G H v ⊆ nbr G (H ∪ S) v from
          fun x hx => mem_filter.mpr ⟨mem_union_left _ (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩))
    · exact (hbad v hv).le.trans (by
        exact_mod_cast card_le_card (show nbr G S v ⊆ nbr G (H ∪ S) v from
          fun x hx => mem_filter.mpr ⟨mem_union_right _ (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩))
  have hd : Disjoint H S := disjoint_left.mpr fun v hvH hvS =>
    (mem_sdiff.mp (hS hvS)).2 hvH
  have hc := hmax (H ∪ S) hU
  rw [card_union_of_disjoint hd] at hc
  have hs := hSne.card_pos
  omega

/-- The extremized preliminary partition has only the conditions used before
connectivity is established. -/
def PreliminaryCandidate {n : ℕ} (G : SimpleGraph (Fin n)) (ε : ℝ)
    (P : Decomposition n) : Prop :=
  (P.X.card : ℝ) ≤ P.parts.card * ε^3 * n ∧
  DegenerateOn G P.Y (3*ε*n) ∧
  (∀ S ∈ P.parts, ∀ v ∈ S,
    3*ε*n - P.parts.card*ε^3*n ≤ ((nbr G S v).card : ℝ)) ∧
  (P.parts.card : ℝ) ≤ ε⁻¹

/-- The numerical reserve in the minimum degree hypothesis. -/
theorem preliminary_reserve {n k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (he : ε ≤ 1/3) (hk : (k : ℝ) ≤ ε⁻¹) :
    k * ε^3 * n ≤ ε^2 * n ∧
    2*ε*n ≤ 3*ε*n - k*ε^3*n ∧
    ε^3*n ≤ 3*ε*n - k*ε^3*n := by
  have hkε : (k : ℝ) * ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hk hε.le
    simpa [inv_mul_cancel₀ hε.ne'] using hh
  have hsq : ε^2 ≤ ε := by nlinarith
  have hcube : ε^3 ≤ ε := by nlinarith [sq_nonneg ε]
  have hfirst : k * ε^3 * n ≤ ε^2 * n := by
    have hh := mul_le_mul_of_nonneg_right hkε (show 0 ≤ ε^2*(n : ℝ) by positivity)
    nlinarith only [hh]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hsqn := mul_le_mul_of_nonneg_right hsq hn0
  have hcuben := mul_le_mul_of_nonneg_right hcube hn0
  constructor
  · exact hfirst
  constructor <;> nlinarith only [hfirst,hsqn,hcuben]

theorem PreliminaryCandidate.part_size {n : ℕ} {G : SimpleGraph (Fin n)}
    {ε : ℝ} {P : Decomposition n} (h : PreliminaryCandidate G ε P)
    (hε : 0 < ε) (he : ε ≤ 1/3) {S : Finset (Fin n)} (hS : S ∈ P.parts) :
    2*ε*n ≤ (S.card : ℝ) := by
  obtain ⟨v,hv⟩ := P.nonempty S hS
  have hr := (preliminary_reserve (n := n) hε he h.2.2.2).2.1
  have hd := h.2.2.1 S hS v hv
  have hu : ((nbr G S v).card : ℝ) + 1 ≤ S.card := by
    exact_mod_cast (Nat.succ_le_iff.mpr (nbr_card_lt G hv))
  linarith only [hr,hd,hu]

theorem PreliminaryCandidate.connectivity_size {n : ℕ} {G : SimpleGraph (Fin n)}
    {ε : ℝ} {P : Decomposition n} (h : PreliminaryCandidate G ε P)
    (hε : 0 < ε) (he : ε ≤ 1/3) {S : Finset (Fin n)} (hS : S ∈ P.parts) :
    ε^3*n ≤ (S.card : ℝ)-1 := by
  obtain ⟨v,hv⟩ := P.nonempty S hS
  have hr := (preliminary_reserve (n := n) hε he h.2.2.2).2.2
  have hd := h.2.2.1 S hS v hv
  have hu : ((nbr G S v).card : ℝ) + 1 ≤ S.card := by
    exact_mod_cast (Nat.succ_le_iff.mpr (nbr_card_lt G hv))
  linarith only [hr,hd,hu]

theorem PreliminaryCandidate.count_slack {n : ℕ} {G : SimpleGraph (Fin n)}
    {ε : ℝ} {P : Decomposition n} (h : PreliminaryCandidate G ε P)
    (hn : 0 < n) (hε : 0 < ε) (he : ε ≤ 1/3) :
    (P.parts.card : ℝ) + 1 ≤ ε⁻¹ := by
  have hsum : (P.parts.card : ℝ)*(2*ε*n) ≤ n := by
    calc
      _ = ∑ _S ∈ P.parts, 2*ε*(n : ℝ) := by simp
      _ ≤ ∑ S ∈ P.parts, (S.card : ℝ) :=
        sum_le_sum fun S hS => h.part_size hε he hS
      _ ≤ n := by exact_mod_cast P.sum_card_parts_le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkε : (P.parts.card : ℝ)*ε ≤ 1/2 := by
    have hh : (2*(P.parts.card : ℝ)*ε)*(n : ℝ) ≤ 1*n := by
      nlinarith only [hsum]
    have hh' := (mul_le_mul_iff_left₀ hnR).mp hh
    linarith only [hh']
  apply (mul_le_mul_iff_left₀ hε).mp
  rw [inv_mul_cancel₀ hε.ne']
  nlinarith only [hkε,he]

theorem preliminary_candidate_exists {n : ℕ} (G : SimpleGraph (Fin n))
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1/3) :
    ∃ P : Decomposition n, PreliminaryCandidate G ε P := by
  classical
  obtain ⟨H,hH,hY⟩ := exists_degree_core G (3*ε*n)
  have hzero : (0 : ℝ) ≤ ε^3*n := by positivity
  have hone : (1 : ℝ) ≤ ε⁻¹ := by
    apply (mul_le_mul_iff_left₀ hε).mp
    rw [inv_mul_cancel₀ hε.ne']
    simpa using le_trans he (by norm_num : (1 : ℝ)/3 ≤ 1)
  by_cases hHne : H.Nonempty
  · refine ⟨Decomposition.single H hHne,?_,hY,?_,?_⟩
    · simp only [Decomposition.single, card_empty, Nat.cast_zero, card_singleton,
        Nat.cast_one, one_mul]
      exact hzero
    · intro S hS v hv
      have hS' : S = H := by simpa [Decomposition.single] using hS
      subst S
      simp only [Decomposition.single, card_singleton, Nat.cast_one, one_mul]
      exact sub_le_self _ hzero |>.trans (hH v hv)
    · simpa [Decomposition.single] using hone
  · have hHe : H = ∅ := not_nonempty_iff_eq_empty.mp hHne
    refine ⟨Decomposition.empty n,?_,?_,?_,?_⟩
    · simp [Decomposition.empty]
    · simpa [Decomposition.empty,hHe] using hY
    · simp [Decomposition.empty]
    · simpa [Decomposition.empty] using (inv_nonneg.mpr hε.le)

/-- Maximizing the number of preliminary pieces forces each piece to be robust. -/
theorem preliminary {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1/3) :
    ∃ P : Decomposition n,
      (P.X.card : ℝ) ≤ ε^2*n ∧
      DegenerateOn G P.Y (3*ε*n) ∧
      (∀ S ∈ P.parts, RealConnected G S (ε^3*n)) ∧
      (∀ S ∈ P.parts, 2*ε*n ≤ (S.card : ℝ)) ∧
      (P.parts.card : ℝ) ≤ ε⁻¹ := by
  classical
  let C : Set (Decomposition n) := {P | PreliminaryCandidate G ε P}
  obtain ⟨P,hP,hmax⟩ := C.exists_max_image (fun P => P.parts.card)
    (Set.toFinite C) (preliminary_candidate_exists G hε he)
  have hP' : PreliminaryCandidate G ε P := hP
  refine ⟨P,hP'.1.trans (preliminary_reserve (n := n) hε he hP'.2.2.2).1,
    hP'.2.1,?_,fun S hS => hP'.part_size hε he hS,hP'.2.2.2⟩
  intro S hS
  by_contra hnot
  obtain ⟨Z,A,B,hZS,hZ,hA,hB,hAB,hcover,hcross⟩ :=
    RealConnected.separator (hP'.connectivity_size hε he hS) hnot
  let Q := P.split hS hA hB hAB hcover hZS
  have hQparts : Q.parts = (P.parts.erase S) ∪ {A,B} := by
    exact Decomposition.split_parts _ _ _ _ _ _ _
  have hQX : Q.X = P.X ∪ Z := by rfl
  have hQY : Q.Y = P.Y := by rfl
  have hQcard : Q.parts.card = P.parts.card+1 :=
    Decomposition.split_card _ _ _ _ _ _ _
  have hAS : A ⊆ S := by
    intro v hv
    exact (mem_sdiff.mp (hcover ▸ mem_union_left B hv)).1
  have hBS : B ⊆ S := by
    intro v hv
    exact (mem_sdiff.mp (hcover ▸ mem_union_right A hv)).1
  have hQ : PreliminaryCandidate G ε Q := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [hQX,hQcard]
      have hc : ((P.X ∪ Z).card : ℝ) ≤ P.X.card + Z.card := by
        exact_mod_cast card_union_le P.X Z
      push_cast
      nlinarith only [hc,hP'.1,hZ]
    · simpa only [hQY] using hP'.2.1
    · intro T hT v hv
      rw [hQparts] at hT
      rw [hQcard]
      push_cast
      rcases mem_union.mp hT with hT | hT
      · have hd := hP'.2.2.1 T (mem_erase.mp hT).2 v hv
        have hnonneg : 0 ≤ ε^3*(n : ℝ) := by positivity
        nlinarith only [hd,hnonneg]
      · rcases mem_insert.mp hT with hTA | hT
        · subst T
          have hd := hP'.2.2.1 S hS v (hAS hv)
          have hl : ((nbr G S v).card : ℝ) ≤ (nbr G A v).card + Z.card := by
            exact_mod_cast nbr_loss G hcover hcross hv
          nlinarith only [hd,hl,hZ]
        · have hTe := mem_singleton.mp hT
          subst T
          have hd := hP'.2.2.1 S hS v (hBS hv)
          have hl : ((nbr G S v).card : ℝ) ≤ (nbr G B v).card + Z.card := by
            exact_mod_cast nbr_loss G (by simpa only [union_comm] using hcover)
              (fun u hu w hw huw => hcross w hw u hu (G.adj_symm huw)) hv
          nlinarith only [hd,hl,hZ]
    · rw [hQcard]
      push_cast
      exact hP'.count_slack hn hε he
  have hh := hmax Q hQ
  rw [hQcard] at hh
  omega

end HadwigerRamsey.ControlledPartition
