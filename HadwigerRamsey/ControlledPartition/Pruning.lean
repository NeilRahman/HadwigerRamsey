import HadwigerRamsey.ControlledPartition.Parameters
import HadwigerRamsey.ControlledPartition.Connectivity

open Finset
open scoped Classical BigOperators

namespace HadwigerRamsey.ControlledPartition

/-- Choose one separator for each unordered pair of robust pieces. -/
theorem symmetric_cuts {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Decomposition n) {s t : ℝ} (hst : s ≤ t)
    (hconn : ∀ S ∈ P.parts, RealConnected G S t)
    (hnomerge : ∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T →
      ¬RealConnected G (S ∪ T) s) :
    ∃ C : Finset (Fin n) → Finset (Fin n) → Finset (Fin n),
      (∀ S T, C S T = C T S) ∧
      (∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T →
        C S T ⊆ S ∪ T ∧ ((C S T).card : ℝ) ≤ s ∧
        ∀ u ∈ S \ C S T, ∀ v ∈ T \ C S T, ¬G.Adj u v) := by
  classical
  have hex : ∀ S T : Finset (Fin n), ∃ Z : Finset (Fin n),
      (S ∈ P.parts ∧ T ∈ P.parts ∧ S ≠ T) →
      Z ⊆ S ∪ T ∧ (Z.card : ℝ) ≤ s ∧
        ∀ u ∈ S \ Z, ∀ v ∈ T \ Z, ¬G.Adj u v := by
    intro S T
    by_cases hh : S ∈ P.parts ∧ T ∈ P.parts ∧ S ≠ T
    · obtain ⟨Z,hZ,hcard,hcross⟩ := RealConnected.union_separator
        (hconn S hh.1) (hconn T hh.2.1) hst (hnomerge S hh.1 T hh.2.1 hh.2.2)
      exact ⟨Z,fun _ => ⟨hZ,hcard.le,hcross⟩⟩
    · exact ⟨∅,fun h => (hh h).elim⟩
  choose Z hZ using hex
  let r := Fintype.equivFin (Finset (Fin n))
  let C := fun S T => if r S < r T then Z S T else Z T S
  have hsym : ∀ S T, C S T = C T S := by
    intro S T
    by_cases he : S = T
    · subst T; rfl
    · have hne : r S ≠ r T := fun hh => he (r.injective hh)
      rcases lt_or_gt_of_ne hne with h | h
      · simp only [C,if_pos h,if_neg (not_lt_of_ge h.le)]
      · simp only [C,if_neg (not_lt_of_ge h.le),if_pos h]
  refine ⟨C,hsym,?_⟩
  intro S hS T hT hST
  by_cases h : r S < r T
  · simpa only [C,if_pos h] using hZ S T ⟨hS,hT,hST⟩
  · have hz := hZ T S ⟨hT,hS,hST.symm⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [C,if_neg h,union_comm] using hz.1
    · simpa only [C,if_neg h] using hz.2.1
    · intro u hu v hv huv
      simp only [C,if_neg h] at hu hv
      exact hz.2.2 v hv u hu (G.adj_symm huv)

/-- Trim the pair separators, preserving all six controlled-partition conditions. -/
theorem prune {n : ℕ} (G : SimpleGraph (Fin n)) {ε η δ : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (he : ε ≤ 1/3) (hδ : 0 < δ)
    (P : Decomposition n)
    (hX : (P.X.card : ℝ) ≤ ε^2*n)
    (hsize : ∀ S ∈ P.parts, 2*ε*n ≤ (S.card : ℝ))
    (hconn : ∀ S ∈ P.parts,
      RealConnected G S ((P.parts.card.factorial : ℝ)*δ*n))
    (hdeg : DegenerateOn G P.Y (3*ε*n))
    (hnb : ∀ v ∈ P.Y, ((nbr G P.core v).card : ℝ) ≤ η*n)
    (hnomerge : ∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T →
      ¬RealConnected G (S ∪ T) (((P.parts.card-1).factorial : ℝ)*δ*n))
    (hδbound : (P.parts.card.factorial : ℝ)*δ ≤ ε^3) :
    ∃ Q : Decomposition n, Controlled G ε η δ Q := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsquare : ε^2 ≤ ε := by nlinarith
  have hcube : ε^3 ≤ ε := by nlinarith [sq_nonneg ε]
  by_cases hzero : P.parts.card = 0
  · have hp : P.parts = ∅ := card_eq_zero.mp hzero
    refine ⟨P,?_,?_,hdeg,hnb,?_,?_⟩
    · exact hX.trans (mul_le_mul_of_nonneg_right hsquare hnR.le)
    · simp [hp]
    · simp [hp]
    · simp [hp]
  let k := P.parts.card
  have hk : 0 < k := Nat.pos_of_ne_zero hzero
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkm : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
    simp only [Nat.cast_sub (Nat.succ_le_iff.mpr hk), Nat.cast_one]
  have hfact : (k.factorial : ℝ) = (k : ℝ)*((k-1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hk)).symm
  have hfacpos : (0 : ℝ) < ((k-1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k-1)
  have hfacone : (1 : ℝ) ≤ ((k-1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k-1)
  let q : ℝ := ((k-1).factorial : ℝ)*δ*n
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqt : q ≤ (k.factorial : ℝ)*δ*n := by
    dsimp [q]
    gcongr
    exact Nat.sub_le k 1
  obtain ⟨C,hCsym,hC⟩ := symmetric_cuts G P hqt hconn hnomerge
  let D : Finset (Fin n) → Finset (Fin n) :=
    fun S => (P.parts.erase S).biUnion fun T => C S T ∩ S
  have hDsub : ∀ S ∈ P.parts, D S ⊆ S := by
    intro S _ v hv
    obtain ⟨T,_,hv⟩ := mem_biUnion.mp hv
    exact (mem_inter.mp hv).2
  let d : ℝ := ((k-1 : ℕ) : ℝ)*q
  have hd : 0 ≤ d := mul_nonneg (Nat.cast_nonneg _) hq
  have hDcard : ∀ S ∈ P.parts, ((D S).card : ℝ) ≤ d := by
    intro S hS
    calc
      _ ≤ ∑ T ∈ P.parts.erase S, ((C S T ∩ S).card : ℝ) := by
        exact_mod_cast (card_biUnion_le :
          ((P.parts.erase S).biUnion fun T => C S T ∩ S).card ≤
            ∑ T ∈ P.parts.erase S, (C S T ∩ S).card)
      _ ≤ ∑ _T ∈ P.parts.erase S, q := by
        apply sum_le_sum
        intro T hT
        obtain ⟨hTS,hT⟩ := mem_erase.mp hT
        have hc := (hC S hS T hT hTS.symm).2.1
        have hi : ((C S T ∩ S).card : ℝ) ≤ (C S T).card := by
          exact_mod_cast card_le_card (inter_subset_left : C S T ∩ S ⊆ C S T)
        exact hi.trans hc
      _ = d := by simp [d,k,q,card_erase_of_mem hS]
  have hgap : δ*n + d ≤ (k.factorial : ℝ)*δ*n := by
    have hh : δ*n ≤ q := by
      dsimp [q]
      nlinarith only [mul_le_mul_of_nonneg_right hfacone
        (show 0 ≤ δ*n by positivity)]
    have heq : (k.factorial : ℝ)*δ*n = q+d := by
      dsimp [q,d]
      rw [hfact,hkm]
      ring
    linarith only [hh,heq]
  have hdub : d ≤ ε^3*n := by
    have hh : (k.factorial : ℝ)*δ*n ≤ ε^3*n :=
      mul_le_mul_of_nonneg_right hδbound hnR.le
    linarith only [hgap,hh,mul_pos hδ hnR]
  have hret : ∀ S ∈ P.parts, ε*n ≤ ((S \ D S).card : ℝ) := by
    intro S hS
    have hc : (S.card : ℝ) ≤ (S \ D S).card + ((D S).card : ℝ) := by
      exact_mod_cast (card_le_card_sdiff_add_card : S.card ≤ (S \ D S).card + (D S).card)
    have hsmall : ((D S).card : ℝ) ≤ ε*n :=
      (hDcard S hS).trans (hdub.trans (mul_le_mul_of_nonneg_right hcube hnR.le))
    linarith only [hc,hsmall,hsize S hS]
  have hne : ∀ S ∈ P.parts, (S \ D S).Nonempty := by
    intro S hS
    have hh : (0 : ℝ) < (S \ D S).card := (mul_pos hε hnR).trans_le (hret S hS)
    exact card_pos.mp (by exact_mod_cast hh)
  let Q := P.trim D hDsub hne
  have hQparts : Q.parts = P.parts.image (fun S => S \ D S) :=
    P.trim_parts D hDsub hne
  have hXQ : (Q.X.card : ℝ) ≤ ε*n := by
    have hc : ((P.parts.biUnion D).card : ℝ) ≤ (k : ℝ)*d := by
      calc
        _ ≤ ∑ S ∈ P.parts, ((D S).card : ℝ) := by exact_mod_cast card_biUnion_le
        _ ≤ ∑ _S ∈ P.parts, d := sum_le_sum hDcard
        _ = _ := by simp [k]
    have hXcard : (Q.X.card : ℝ) ≤ P.X.card + ((P.parts.biUnion D).card : ℝ) := by
      exact_mod_cast (card_union_le P.X (P.parts.biUnion D))
    have hkε : (k : ℝ)*ε ≤ 1 := by
      have hb := (parts_bound hn hε P hsize).2
      have hh := mul_le_mul_of_nonneg_right hb hε.le
      simpa only [inv_mul_cancel₀ hε.ne'] using hh
    have hkδ : (k : ℝ)*d ≤ ε^2*n := by
      have hh := mul_le_mul_of_nonneg_left hdub hkR.le
      have hh' := mul_le_mul_of_nonneg_right hkε
        (show 0 ≤ ε^2*n by positivity)
      nlinarith only [hh,hh']
    have hfinal : 2*ε^2*n ≤ ε*n := by
      have hsmall : 2*ε^2 ≤ ε := by nlinarith
      exact mul_le_mul_of_nonneg_right hsmall hnR.le
    linarith only [hc,hXcard,hX,hkδ,hfinal]
  refine ⟨Q,hXQ,?_,?_,?_,?_,?_⟩
  · intro R hR
    rw [hQparts] at hR
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hR
    apply ((hconn S hS).delete (D S)).mono
    have hc := hDcard S hS
    linarith only [hc,hgap]
  · exact hdeg
  · intro v hv
    have hc : ((nbr G Q.core v).card : ℝ) ≤ (nbr G P.core v).card := by
      exact_mod_cast card_le_card (nbr_mono G (P.trim_core_subset D hDsub hne) v)
    exact hc.trans (hnb v hv)
  · intro R hR
    rw [hQparts] at hR
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hR
    exact hret S hS
  · intro R hR U hU hRU u hu v hv
    rw [hQparts] at hR
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hR
    rw [hQparts] at hU
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hU
    have hST : S ≠ T := fun hh => hRU (congrArg (fun A => A \ D A) hh)
    have huC : u ∉ C S T := by
      intro huC
      apply (mem_sdiff.mp hu).2
      exact mem_biUnion.mpr ⟨T,mem_erase.mpr ⟨hST.symm,hT⟩,
        mem_inter.mpr ⟨huC,(mem_sdiff.mp hu).1⟩⟩
    have hvC : v ∉ C S T := by
      intro hvC
      apply (mem_sdiff.mp hv).2
      exact mem_biUnion.mpr ⟨S,mem_erase.mpr ⟨hST,hS⟩,
        mem_inter.mpr ⟨(hCsym S T) ▸ hvC,(mem_sdiff.mp hv).1⟩⟩
    exact (hC S hS T hT hST).2.2 u
      (mem_sdiff.mpr ⟨(mem_sdiff.mp hu).1,huC⟩) v
      (mem_sdiff.mpr ⟨(mem_sdiff.mp hv).1,hvC⟩)

end HadwigerRamsey.ControlledPartition
