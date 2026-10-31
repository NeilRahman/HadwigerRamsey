import Mathlib

open scoped BigOperators
open Finset

namespace HadwigerRamsey

/-- A relation without two pairs differing in both coordinates lies in one row or column. -/
lemma supported_on_row_or_column {I J : Type*} [Nonempty I] (R : I → J → Prop)
    (h : ∀ i j i' j', R i j → R i' j' → i = i' ∨ j = j') :
    (∃ i, ∀ i' j, R i' j → i' = i) ∨ (∃ j, ∀ i j', R i j' → j' = j) := by
  classical
  by_cases hR : ∃ i j, R i j
  · obtain ⟨i, j, hij⟩ := hR
    by_cases hrow : ∀ i' j', R i' j' → i' = i
    · exact Or.inl ⟨i, hrow⟩
    · push_neg at hrow
      obtain ⟨i', j', hi'j', hne⟩ := hrow
      have hj' : j' = j := (h i' j' i j hi'j' hij).resolve_left hne
      subst j'
      right
      refine ⟨j, ?_⟩
      intro a b hab
      by_contra hb
      have ha : a = i := (h a b i j hab hij).resolve_right hb
      have ha' : a = i' := (h a b i' j hab hi'j').resolve_right hb
      exact hne (ha'.symm.trans ha)
  · exact Or.inl ⟨Classical.choice inferInstance, fun i j hij => (hR ⟨i,j,hij⟩).elim⟩

/-- Counting intersections with the parts of a Mathlib finite partition. -/
lemma sum_card_inter_parts {α : Type*} [DecidableEq α] {s a : Finset α}
    (P : Finpartition s) (ha : a ⊆ s) :
    ∑ b ∈ P.parts, (a ∩ b).card = a.card := by
  have hdisj : (↑P.parts : Set (Finset α)).PairwiseDisjoint (fun b => a ∩ b) := by
    intro b hb c hc hbc
    exact (P.disjoint hb hc hbc).mono inter_subset_right inter_subset_right
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext x
  simp only [mem_biUnion, mem_inter]
  constructor
  · rintro ⟨b, hb, hx, hxb⟩
    exact hx
  · intro hx
    obtain ⟨b, hb, hxb⟩ := P.exists_mem (ha hx)
    exact ⟨b, hb, hx, hxb⟩

/-- If every large intersection lies in one specified part, that part is large. -/
lemma large_part_of_small_other_intersections {α : Type*} [DecidableEq α]
    {s : Finset α} (P Q : Finpartition s) {k : ℕ} (hP : P.parts.card ≤ k)
    (hQ : Q.parts.card ≤ k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε)
    {p : Finset α} (hp : p ∈ P.parts)
    (hsmall : ∀ a ∈ P.parts, a ≠ p → ∀ b ∈ Q.parts,
      ((a ∩ b).card : ℝ) < ε / (k : ℝ)^2 * s.card) :
    (1-ε) * (s.card : ℝ) ≤ p.card := by
  classical
  let t : ℝ := ε / (k : ℝ)^2 * s.card
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrows : ∀ a ∈ P.parts.erase p, (a.card : ℝ) ≤ Q.parts.card * t := by
    intro a ha
    have har := mem_erase.mp ha
    rw [← sum_card_inter_parts Q (P.subset har.2), Nat.cast_sum]
    calc
      _ ≤ ∑ _b ∈ Q.parts, t := Finset.sum_le_sum (fun b hb => (hsmall a har.2 har.1 b hb).le)
      _ = _ := by simp
  have hsum : (∑ a ∈ P.parts.erase p, (a.card : ℝ)) + p.card = s.card := by
    rw [Finset.sum_erase_add _ _ hp, ← Nat.cast_sum, P.sum_card_parts]
  have hbound : (∑ a ∈ P.parts.erase p, (a.card : ℝ)) ≤ ε * s.card := by
    calc
      _ ≤ ∑ _a ∈ P.parts.erase p, (Q.parts.card : ℝ) * t := Finset.sum_le_sum hrows
      _ = (P.parts.erase p).card * ((Q.parts.card : ℝ) * t) := by simp
      _ ≤ (k : ℝ) * ((k : ℝ) * t) := by
        gcongr
        · exact_mod_cast (Finset.card_erase_le.trans hP)
      _ = ε * s.card := by dsimp [t]; field_simp
  nlinarith only [hsum, hbound]

/-- Lemma 3.1 (`bigset`) on a nonempty ground set. The two small sets can
be taken to be intersections of parts of Mathlib's existing finite partitions. -/
theorem bigset {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    (P Q : Finpartition s) {k : ℕ} (hP : P.parts.card ≤ k) (hQ : Q.parts.card ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    (∃ p ∈ P.parts, (1-ε) * (s.card : ℝ) ≤ p.card) ∨
    (∃ q ∈ Q.parts, (1-ε) * (s.card : ℝ) ≤ q.card) ∨
    (∃ A B : Finset α,
      ε / (k : ℝ)^2 * s.card ≤ A.card ∧
      ε / (k : ℝ)^2 * s.card ≤ B.card ∧
      (∃ pA ∈ P.parts, ∃ pB ∈ P.parts, A ⊆ pA ∧ B ⊆ pB ∧ pA ≠ pB) ∧
      (∃ qA ∈ Q.parts, ∃ qB ∈ Q.parts, A ⊆ qA ∧ B ⊆ qB ∧ qA ≠ qB)) := by
  classical
  have hPn : P.parts.Nonempty := P.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hs)
  have hk : 0 < k := lt_of_lt_of_le hPn.card_pos hP
  letI : Nonempty P.parts := hPn.to_subtype
  let R : P.parts → Q.parts → Prop := fun p q =>
    ε / (k : ℝ)^2 * s.card ≤ (p.val ∩ q.val).card
  by_cases hpair : ∃ p : P.parts, ∃ q : Q.parts, ∃ p' : P.parts, ∃ q' : Q.parts,
      R p q ∧ R p' q' ∧ p ≠ p' ∧ q ≠ q'
  · obtain ⟨p,q,p',q',hp,hp',hne,hne'⟩ := hpair
    right; right
    refine ⟨p.val ∩ q.val, p'.val ∩ q'.val, hp, hp', ?_, ?_⟩
    · exact ⟨p.val, p.property, p'.val, p'.property, inter_subset_left, inter_subset_left,
        fun h => hne (Subtype.ext h)⟩
    · exact ⟨q.val, q.property, q'.val, q'.property, inter_subset_right, inter_subset_right,
        fun h => hne' (Subtype.ext h)⟩
  · have hmatch : ∀ p q p' q', R p q → R p' q' → p = p' ∨ q = q' := by
      intro p q p' q' hp hp'
      by_contra h
      push_neg at h
      exact hpair ⟨p,q,p',q',hp,hp',h⟩
    rcases supported_on_row_or_column R hmatch with ⟨p,hrow⟩ | ⟨q,hcol⟩
    · left
      refine ⟨p.val, p.property, large_part_of_small_other_intersections P Q hP hQ hk ε hε p.property ?_⟩
      intro a ha hne b hb
      apply lt_of_not_ge
      intro hab
      exact hne (congrArg Subtype.val (hrow ⟨a,ha⟩ ⟨b,hb⟩ hab))
    · right; left
      refine ⟨q.val, q.property, large_part_of_small_other_intersections Q P hQ hP hk ε hε q.property ?_⟩
      intro b hb hne a ha
      apply lt_of_not_ge
      intro hab
      have hab' : R ⟨a,ha⟩ ⟨b,hb⟩ := by dsimp [R]; simpa only [inter_comm] using hab
      exact hne (congrArg Subtype.val (hcol ⟨a,ha⟩ ⟨b,hb⟩ hab'))

end HadwigerRamsey
