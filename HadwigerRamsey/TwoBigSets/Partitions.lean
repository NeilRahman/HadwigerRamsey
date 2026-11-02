import HadwigerRamsey.BigSet
import HadwigerRamsey.ControlledPartition.Interpretation

open Finset
open scoped Classical BigOperators
namespace HadwigerRamsey.TwoBigSets
open ControlledPartition

lemma family_disjoint {n : ℕ} (P : Decomposition n) :
    (↑(insert P.Y P.parts) : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro S hS T hT hST
  rcases mem_insert.mp hS with rfl | hS <;> rcases mem_insert.mp hT with rfl | hT
  · exact (hST rfl).elim
  · exact (P.disjoint_Y T hT).symm
  · exact P.disjoint_Y S hS
  · exact P.pairwise hS hT hST

lemma family_cover {n : ℕ} (P : Decomposition n) {v : Fin n} (hv : v ∉ P.X) :
    ∃ S ∈ insert P.Y P.parts, v ∈ S := by
  have hc : v ∈ P.parts.biUnion id ∪ P.X ∪ P.Y := by rw [P.cover]; simp
  rcases mem_union.mp hc with hc | hy
  · rcases mem_union.mp hc with hc | hx
    · obtain ⟨S,hS,hvS⟩ := mem_biUnion.mp hc
      exact ⟨S,mem_insert_of_mem hS,hvS⟩
    · exact (hv hx).elim
  · exact ⟨P.Y,mem_insert_self _ _,hy⟩

noncomputable def restricted {n : ℕ} (P : Decomposition n) (W : Finset (Fin n))
    (hWX : Disjoint W P.X) : Finpartition W where
  parts := ((insert P.Y P.parts).image (fun S => S ∩ W)).erase ∅
  supIndep := by
    apply Finset.supIndep_iff_pairwiseDisjoint.mpr
    intro S hS T hT hST
    obtain ⟨S',hS',rfl⟩ := mem_image.mp (mem_erase.mp hS).2
    obtain ⟨T',hT',rfl⟩ := mem_image.mp (mem_erase.mp hT).2
    exact (family_disjoint P hS' hT' (fun he => hST (congrArg (fun U => U ∩ W) he))).mono
      inter_subset_left inter_subset_left
  sup_parts := by
    ext v
    simp only [mem_sup,id_eq,mem_erase,mem_image]
    constructor
    · rintro ⟨S,⟨_,S',_,rfl⟩,hv⟩
      exact (mem_inter.mp hv).2
    · intro hv
      obtain ⟨S,hS,hvS⟩ := family_cover P (fun hx => disjoint_left.mp hWX hv hx)
      refine ⟨S ∩ W,⟨?_,⟨S,hS,rfl⟩⟩,mem_inter.mpr ⟨hvS,hv⟩⟩
      exact nonempty_iff_ne_empty.mp ⟨v,mem_inter.mpr ⟨hvS,hv⟩⟩
  bot_notMem := notMem_erase _ _

lemma restricted_origin {n : ℕ} (P : Decomposition n) (W : Finset (Fin n))
    (hWX : Disjoint W P.X) {S : Finset (Fin n)} (hS : S ∈ (restricted P W hWX).parts) :
    ∃ T ∈ insert P.Y P.parts, S = T ∩ W := by
  obtain ⟨T,hT,he⟩ := mem_image.mp (mem_erase.mp hS).2
  exact ⟨T,hT,he.symm⟩

lemma restricted_card {n : ℕ} (P : Decomposition n) (W : Finset (Fin n))
    (hWX : Disjoint W P.X) :
    (restricted P W hWX).parts.card ≤ P.parts.card+1 := by
  exact (card_erase_le.trans (card_image_le)).trans (card_insert_le _ _)

lemma balanced_subsets {n : ℕ} {A B : Finset (Fin n)} {L : ℝ}
    (hAB : Disjoint A B) (hA : L ≤ (A.card : ℝ)) (hB : L ≤ (B.card : ℝ)) :
    ∃ A' B', A' ⊆ A ∧ B' ⊆ B ∧ Disjoint A' B' ∧ A'.card = B'.card ∧ L ≤ (A'.card : ℝ) := by
  let a := min A.card B.card
  obtain ⟨A',hA',hca⟩ := exists_subset_card_eq (min_le_left A.card B.card)
  obtain ⟨B',hB',hcb⟩ := exists_subset_card_eq (min_le_right A.card B.card)
  refine ⟨A',B',hA',hB',hAB.mono hA' hB',hca.trans hcb.symm,?_⟩
  rw [hca]
  exact_mod_cast (show L ≤ (min A.card B.card : ℝ) by simpa only [Nat.cast_min] using le_min hA hB)

lemma coefficient_lower {r : ℝ} (hr : 0 < r) (hsmall : r ≤ 1/20)
    {k : ℕ} (hk : (k : ℝ) ≤ r⁻¹+1) (hkpos : 0 < k)
    {n w : ℕ} (hw : (1-2*r)*n ≤ (w : ℝ)) :
    r^3/2*n ≤ r/(k : ℝ)^2*w := by
  have hkr : (k : ℝ)*r ≤ 1+r := by
    have hh := mul_le_mul_of_nonneg_right hk hr.le
    simpa only [add_mul,inv_mul_cancel₀ hr.ne',one_mul] using hh
  have hsq : (k : ℝ)^2*r^2 ≤ (1+r)^2 := by
    have hh := mul_self_le_mul_self (by positivity : 0 ≤ (k:ℝ)*r) hkr
    nlinarith only [hh]
  have hr2 : r^2 ≤ r/20 := by nlinarith
  have hpoly : (1+r)^2 ≤ 2*(1-2*r) := by nlinarith
  have hc := mul_le_mul_of_nonneg_left (hsq.trans hpoly) (hr.le : 0 ≤ r)
  have hcoef : r^3/2*(k : ℝ)^2 ≤ r*(1-2*r) := by nlinarith only [hc]
  have hmult := mul_le_mul_of_nonneg_right hcoef (show (0:ℝ) ≤ n by positivity)
  have hwmult := mul_le_mul_of_nonneg_left hw hr.le
  have hden : 0 < (k : ℝ)^2 := by positivity
  calc
    _ ≤ r*(w : ℝ)/(k : ℝ)^2 := (le_div_iff₀ hden).mpr (by nlinarith only [hmult,hwmult])
    _ = _ := by ring

/-- Restrict the controlled partitions, apply Lemma 3.1, and balance its two sets. -/
theorem large_separated_sets {n : ℕ} (G H : SimpleGraph (Fin n))
    (P Q : Decomposition n) {r ε η δ : ℝ} (hn : 0 < n)
    (hr : 0 < r) (hrs : r ≤ 1/20)
    (hgap : 1-ε < (1-r)*(1-2*r))
    (hP : Controlled G r η δ P) (hQ : Controlled H r η δ Q)
    (hPs : ∀ S ∈ insert P.Y P.parts, (S.card : ℝ) ≤ (1-ε)*n)
    (hQs : ∀ S ∈ insert Q.Y Q.parts, (S.card : ℝ) ≤ (1-ε)*n) :
    ∃ A B : Finset (Fin n), Disjoint A B ∧ A.card = B.card ∧
      r^3/2*n ≤ (A.card : ℝ) ∧
      (∃ S ∈ insert P.Y P.parts, ∃ T ∈ insert P.Y P.parts,
        A ⊆ S ∧ B ⊆ T ∧ S ≠ T) ∧
      (∃ S ∈ insert Q.Y Q.parts, ∃ T ∈ insert Q.Y Q.parts,
        A ⊆ S ∧ B ⊆ T ∧ S ≠ T) := by
  classical
  let W : Finset (Fin n) := (univ \ P.X) \ Q.X
  have hWP : Disjoint W P.X := by
    apply disjoint_left.mpr
    intro v hv hx
    exact (mem_sdiff.mp (mem_sdiff.mp hv).1).2 hx
  have hWQ : Disjoint W Q.X := by
    apply disjoint_left.mpr
    intro v hv hx
    exact (mem_sdiff.mp hv).2 hx
  have hW : (1-2*r)*n ≤ (W.card : ℝ) := by
    have hc1 := (card_le_card_sdiff_add_card : (univ : Finset (Fin n)).card ≤ (univ \ P.X).card + P.X.card)
    have hc2 := (card_le_card_sdiff_add_card : ((univ : Finset (Fin n)) \ P.X).card ≤ W.card + Q.X.card)
    have hc1R : (n : ℝ) ≤ (univ \ P.X).card + (P.X.card : ℝ) := by
      have hh : n ≤ (univ \ P.X).card + P.X.card := by simpa only [card_univ,Fintype.card_fin] using hc1
      exact_mod_cast hh
    have hc2R : ((univ \ P.X).card : ℝ) ≤ W.card + (Q.X.card : ℝ) := by exact_mod_cast hc2
    nlinarith only [hc1R,hc2R,hP.1,hQ.1]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hWpos : 0 < W.card := by
    have hh : (0 : ℝ) < W.card := lt_of_lt_of_le (by nlinarith : 0 < (1-2*r)*n) hW
    exact_mod_cast hh
  let PP := restricted P W hWP
  let QQ := restricted Q W hWQ
  let k := max P.parts.card Q.parts.card + 1
  have hkpos : 0 < k := by dsimp [k]; omega
  have hk : (k : ℝ) ≤ r⁻¹+1 := by
    have hkp := hP.card_parts_le hn hr
    have hkq := hQ.card_parts_le hn hr
    dsimp [k]
    push_cast
    have hh := max_le hkp hkq
    linarith only [hh]
  have hPP : PP.parts.card ≤ k := (restricted_card P W hWP).trans (by dsimp [k]; omega)
  have hQQ : QQ.parts.card ≤ k := (restricted_card Q W hWQ).trans (by dsimp [k]; omega)
  have hlarge : ∀ R : Decomposition n, ∀ hRX : Disjoint W R.X,
      (∀ S ∈ insert R.Y R.parts, (S.card : ℝ) ≤ (1-ε)*n) →
      ∀ S ∈ (restricted R W hRX).parts, (S.card : ℝ) < (1-r)*W.card := by
    intro R hRX hRs S hS
    obtain ⟨T,hT,rfl⟩ := restricted_origin R W hRX hS
    have hc : ((T ∩ W).card : ℝ) ≤ T.card := by exact_mod_cast card_le_card inter_subset_left
    have hgapn := mul_lt_mul_of_pos_right hgap hnR
    have hw := mul_le_mul_of_nonneg_left hW (by linarith : 0 ≤ 1-r)
    nlinarith only [hc,hRs T hT,hgapn,hw]
  obtain hbig | hbig | ⟨A,B,hA,hB,hABP,hABQ⟩ :=
    bigset (card_pos.mp hWpos) PP QQ hPP hQQ r hr
  · obtain ⟨S,hS,hb⟩ := hbig
    exact (not_le_of_gt (hlarge P hWP hPs S hS) hb).elim
  · obtain ⟨S,hS,hb⟩ := hbig
    exact (not_le_of_gt (hlarge Q hWQ hQs S hS) hb).elim
  · obtain ⟨SP,hSP,TP,hTP,hASP,hBTP,hneP⟩ := hABP
    obtain ⟨SQ,hSQ,TQ,hTQ,hASQ,hBTQ,hneQ⟩ := hABQ
    have hAB : Disjoint A B := (PP.disjoint hSP hTP hneP).mono hASP hBTP
    have hcoef := coefficient_lower hr hrs hk hkpos hW
    obtain ⟨A',B',hA'A,hB'B,hd,hcard,hsize⟩ := balanced_subsets hAB (hcoef.trans hA) (hcoef.trans hB)
    obtain ⟨SP',hSP',heSP⟩ := restricted_origin P W hWP hSP
    obtain ⟨TP',hTP',heTP⟩ := restricted_origin P W hWP hTP
    obtain ⟨SQ',hSQ',heSQ⟩ := restricted_origin Q W hWQ hSQ
    obtain ⟨TQ',hTQ',heTQ⟩ := restricted_origin Q W hWQ hTQ
    refine ⟨A',B',hd,hcard,hsize,?_,?_⟩
    · refine ⟨SP',hSP',TP',hTP',?_,?_,?_⟩
      · exact hA'A.trans (hASP.trans (by rw [heSP]; exact inter_subset_left))
      · exact hB'B.trans (hBTP.trans (by rw [heTP]; exact inter_subset_left))
      · intro hh
        exact hneP (by rw [heSP,heTP,hh])
    · refine ⟨SQ',hSQ',TQ',hTQ',?_,?_,?_⟩
      · exact hA'A.trans (hASQ.trans (by rw [heSQ]; exact inter_subset_left))
      · exact hB'B.trans (hBTQ.trans (by rw [heTQ]; exact inter_subset_left))
      · intro hh
        exact hneQ (by rw [heSQ,heTQ,hh])

end HadwigerRamsey.TwoBigSets
