import HadwigerRamsey.ControlledPartition.Definitions

open Finset
open scoped Classical

namespace HadwigerRamsey.ControlledPartition
namespace Decomposition
variable {n : ℕ}

instance : Finite (Decomposition n) :=
  Finite.of_injective (fun P : Decomposition n => (P.parts,P.X,P.Y)) (by
    intro P Q h
    cases P
    cases Q
    cases h
    rfl)

noncomputable instance : Fintype (Decomposition n) := Fintype.ofFinite _


@[simp] theorem mem_core (P : Decomposition n) (v : Fin n) :
    v ∈ P.core ↔ ∃ S ∈ P.parts, v ∈ S := by simp [core]

theorem subset_core (P : Decomposition n) {S : Finset (Fin n)} (hS : S ∈ P.parts) :
    S ⊆ P.core := by intro v hv; exact (mem_core P v).2 ⟨S,hS,hv⟩

theorem core_disjoint_X (P : Decomposition n) : Disjoint P.core P.X := by
  rw [Finset.disjoint_left]
  rintro v hv hx
  obtain ⟨S,hS,hv⟩ := (mem_core P v).1 hv
  exact Finset.disjoint_left.mp (P.disjoint_X S hS) hv hx

theorem core_disjoint_Y (P : Decomposition n) : Disjoint P.core P.Y := by
  rw [Finset.disjoint_left]
  rintro v hv hy
  obtain ⟨S,hS,hv⟩ := (mem_core P v).1 hv
  exact Finset.disjoint_left.mp (P.disjoint_Y S hS) hv hy

theorem sum_card_parts_le (P : Decomposition n) :
    ∑ S ∈ P.parts, S.card ≤ n := by
  have hh : (∑ S ∈ P.parts, S.card) = P.core.card := by simpa [core] using (Finset.card_biUnion P.pairwise).symm
  rw [hh]
  exact (card_le_card (subset_univ _)).trans_eq (by simp)

theorem card_core (P : Decomposition n) :
    P.core.card = ∑ S ∈ P.parts, S.card := Finset.card_biUnion P.pairwise

noncomputable def empty (n : ℕ) : Decomposition n where
  parts := ∅
  X := ∅
  Y := univ
  nonempty := by simp
  pairwise := by simp
  disjoint_X := by simp
  disjoint_Y := by simp
  disjoint_XY := by simp
  cover := by simp

noncomputable def single (S : Finset (Fin n)) (hS : S.Nonempty) : Decomposition n where
  parts := {S}
  X := ∅
  Y := univ \ S
  nonempty := by simpa using hS
  pairwise := by simp
  disjoint_X := by simp
  disjoint_Y := by simpa using (disjoint_sdiff_self_right : Disjoint S (univ \ S))
  disjoint_XY := by simp
  cover := by simp

/-- Replace some old pieces by a partition of their vertices except for a
new exceptional set. -/
noncomputable def replace (P : Decomposition n)
    (R Q : Finset (Finset (Fin n))) (Z : Finset (Fin n))
    (hR : R ⊆ P.parts) (hQ : ∀ S ∈ Q, S.Nonempty)
    (hQpair : (Q : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hcover : Q.biUnion id ∪ Z = R.biUnion id)
    (hdis : Disjoint (Q.biUnion id) Z) : Decomposition n where
  parts := (P.parts \ R) ∪ Q
  X := P.X ∪ Z
  Y := P.Y
  nonempty := by
    intro S hS
    rcases mem_union.mp hS with hS | hS
    · exact P.nonempty S (mem_sdiff.mp hS).1
    · exact hQ S hS
  pairwise := by
    intro S hS T hT hST
    have hQsub : ∀ U ∈ Q, U ⊆ R.biUnion id := by
      intro U hU v hv
      rw [← hcover]
      exact mem_union_left _ (mem_biUnion.mpr ⟨U,hU,hv⟩)
    have cross : ∀ U ∈ P.parts \ R, ∀ V ∈ Q, Disjoint U V := by
      intro U hU V hV
      rw [disjoint_left]
      intro v hvU hvV
      obtain ⟨W,hW,hvW⟩ := mem_biUnion.mp (hQsub V hV hvV)
      exact disjoint_left.mp (P.pairwise (mem_sdiff.mp hU).1 (hR hW)
        (fun he => (mem_sdiff.mp hU).2 (he ▸ hW))) hvU hvW
    rcases mem_union.mp hS with hS | hS <;> rcases mem_union.mp hT with hT | hT
    · exact P.pairwise (mem_sdiff.mp hS).1 (mem_sdiff.mp hT).1 hST
    · exact cross S hS T hT
    · exact (cross T hT S hS).symm
    · exact hQpair hS hT hST
  disjoint_X := by
    intro S hS
    rw [disjoint_union_right]
    have hSsub : S ⊆ P.core := by
      rcases mem_union.mp hS with hS | hS
      · exact P.subset_core (mem_sdiff.mp hS).1
      · intro v hv
        have : v ∈ R.biUnion id := by rw [← hcover]; exact mem_union_left _ (mem_biUnion.mpr ⟨S,hS,hv⟩)
        obtain ⟨T,hT,hvT⟩ := mem_biUnion.mp this
        exact P.subset_core (hR hT) hvT
    refine ⟨P.core_disjoint_X.mono_left hSsub,?_⟩
    rcases mem_union.mp hS with hS | hS
    · rw [disjoint_left]
      intro v hv hz
      have : v ∈ R.biUnion id := by rw [← hcover]; exact mem_union_right _ hz
      obtain ⟨T,hT,hvT⟩ := mem_biUnion.mp this
      exact disjoint_left.mp (P.pairwise (mem_sdiff.mp hS).1 (hR hT)
        (fun he => (mem_sdiff.mp hS).2 (he ▸ hT))) hv hvT
    · exact hdis.mono_left (by intro v hv; exact mem_biUnion.mpr ⟨S,hS,hv⟩)
  disjoint_Y := by
    intro S hS
    apply P.core_disjoint_Y.mono_left
    intro v hv
    rcases mem_union.mp hS with hS | hS
    · exact P.subset_core (mem_sdiff.mp hS).1 hv
    · have : v ∈ R.biUnion id := by rw [← hcover]; exact mem_union_left _ (mem_biUnion.mpr ⟨S,hS,hv⟩)
      obtain ⟨T,hT,hvT⟩ := mem_biUnion.mp this
      exact P.subset_core (hR hT) hvT
  disjoint_XY := by
    rw [disjoint_union_left]
    refine ⟨P.disjoint_XY, P.core_disjoint_Y.mono_left ?_⟩
    intro v hv
    have : v ∈ R.biUnion id := by rw [← hcover]; exact mem_union_right _ hv
    obtain ⟨T,hT,hvT⟩ := mem_biUnion.mp this
    exact P.subset_core (hR hT) hvT
  cover := by
    ext v
    have hc : v ∈ P.parts.biUnion id ∪ P.X ∪ P.Y := by rw [P.cover]; simp
    have hr : v ∈ Q.biUnion id ∪ Z ↔ v ∈ R.biUnion id := by rw [hcover]
    simp only [mem_union, mem_biUnion, mem_sdiff, id_eq, mem_univ] at *
    constructor
    · intro _; trivial
    · intro _
      rcases hc with (⟨S,hS,hv⟩ | hx) | hy
      · by_cases hsR : S ∈ R
        · have hr' : (∃ S, S ∈ Q ∧ v ∈ S) ∨ v ∈ Z := by apply hr.mpr; exact ⟨S,hsR,hv⟩
          rcases hr' with ⟨T,hT,hvT⟩ | hz
          · exact Or.inl (Or.inl ⟨T,Or.inr hT,hvT⟩)
          · exact Or.inl (Or.inr (Or.inr hz))
        · exact Or.inl (Or.inl ⟨S,Or.inl ⟨hS,hsR⟩,hv⟩)
      · exact Or.inl (Or.inr (Or.inl hx))
      · exact Or.inr hy

 theorem replace_card (P : Decomposition n)
    (R Q : Finset (Finset (Fin n))) (Z : Finset (Fin n))
    (hR : R ⊆ P.parts) (hQ : ∀ S ∈ Q, S.Nonempty)
    (hQpair : (Q : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hcover : Q.biUnion id ∪ Z = R.biUnion id)
    (hdis : Disjoint (Q.biUnion id) Z) :
    (P.replace R Q Z hR hQ hQpair hcover hdis).parts.card = P.parts.card - R.card + Q.card := by
  have hd : Disjoint (P.parts \ R) Q := by
    rw [disjoint_left]
    intro S hS hSQ
    obtain ⟨v,hv⟩ := hQ S hSQ
    have hvR : v ∈ R.biUnion id := by rw [←hcover]; exact mem_union_left _ (mem_biUnion.mpr ⟨S,hSQ,hv⟩)
    obtain ⟨T,hT,hvT⟩ := mem_biUnion.mp hvR
    exact disjoint_left.mp (P.pairwise (mem_sdiff.mp hS).1 (hR hT)
      (fun he => (mem_sdiff.mp hS).2 (he ▸ hT))) hv hvT
  dsimp [replace]
  rw [card_union_of_disjoint hd, card_sdiff_of_subset hR]


noncomputable def split (P : Decomposition n) {S A B Z : Finset (Fin n)}
    (hS : S ∈ P.parts) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hcover : A ∪ B = S \ Z) (hZ : Z ⊆ S) : Decomposition n :=
  P.replace {S} {A,B} Z (by simpa) (by
    intro T hT
    simp only [mem_insert,mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact hA
    · exact hB) (by
      intro T hT U hU hTU
      simp only [mem_coe,mem_insert,mem_singleton] at hT hU
      rcases hT with rfl | rfl <;> rcases hU with rfl | rfl
      · exact (hTU rfl).elim
      · exact hAB
      · exact hAB.symm
      · exact (hTU rfl).elim) (by
        simpa only [biUnion_insert,singleton_biUnion,id_eq] using (by
          rw [hcover, sdiff_union_of_subset hZ] : A ∪ B ∪ Z = S)) (by
        simpa only [biUnion_insert,singleton_biUnion,id_eq,hcover] using sdiff_disjoint)

@[simp] theorem split_parts (P : Decomposition n) {S A B Z : Finset (Fin n)}
    (hS : S ∈ P.parts) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hcover : A ∪ B = S \ Z) (hZ : Z ⊆ S) :
    (P.split hS hA hB hAB hcover hZ).parts = (P.parts.erase S) ∪ {A,B} := by
  simp [split,replace,sdiff_singleton_eq_erase]

@[simp] theorem split_X (P : Decomposition n) {S A B Z : Finset (Fin n)}
    (hS : S ∈ P.parts) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hcover : A ∪ B = S \ Z) (hZ : Z ⊆ S) :
    (P.split hS hA hB hAB hcover hZ).X = P.X ∪ Z := rfl

@[simp] theorem split_Y (P : Decomposition n) {S A B Z : Finset (Fin n)}
    (hS : S ∈ P.parts) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hcover : A ∪ B = S \ Z) (hZ : Z ⊆ S) :
    (P.split hS hA hB hAB hcover hZ).Y = P.Y := rfl

@[simp] theorem split_card (P : Decomposition n) {S A B Z : Finset (Fin n)}
    (hS : S ∈ P.parts) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hcover : A ∪ B = S \ Z) (hZ : Z ⊆ S) :
    (P.split hS hA hB hAB hcover hZ).parts.card = P.parts.card+1 := by
  have hne : A ≠ B := by
    intro he
    obtain ⟨v,hv⟩ := hA
    exact disjoint_left.mp hAB hv (he ▸ hv)
  change (P.replace _ _ _ _ _ _ _ _).parts.card = _
  erw [P.replace_card]
  have hc : 0 < P.parts.card := card_pos.mpr ⟨S,hS⟩
  have htwo : ({A,B}:Finset (Finset (Fin n))).card = 2 := by simp [hne]
  simp only [card_singleton,htwo] 
  omega


noncomputable def merge (P : Decomposition n) {S T : Finset (Fin n)}
    (hS : S ∈ P.parts) (hT : T ∈ P.parts) (hST : S ≠ T) : Decomposition n :=
  P.replace {S,T} {S∪T} ∅ (by intro U hU; rcases mem_insert.mp hU with rfl | hU; exact hS; exact mem_singleton.mp hU ▸ hT) (by
    intro U hU
    have he : U = S ∪ T := mem_singleton.mp hU
    rw [he]
    exact (P.nonempty S hS).mono subset_union_left) (by simp) (by simp) (by simp)

@[simp] theorem merge_parts (P : Decomposition n) {S T : Finset (Fin n)}
    (hS : S ∈ P.parts) (hT : T ∈ P.parts) (hST : S ≠ T) :
    (P.merge hS hT hST).parts = (P.parts \ {S,T}) ∪ {S∪T} := rfl

@[simp] theorem merge_X (P : Decomposition n) {S T : Finset (Fin n)}
    (hS : S ∈ P.parts) (hT : T ∈ P.parts) (hST : S ≠ T) :
    (P.merge hS hT hST).X = P.X := by simp [merge,replace]

@[simp] theorem merge_Y (P : Decomposition n) {S T : Finset (Fin n)}
    (hS : S ∈ P.parts) (hT : T ∈ P.parts) (hST : S ≠ T) :
    (P.merge hS hT hST).Y = P.Y := rfl

@[simp] theorem merge_card (P : Decomposition n) {S T : Finset (Fin n)}
    (hS : S ∈ P.parts) (hT : T ∈ P.parts) (hST : S ≠ T) :
    (P.merge hS hT hST).parts.card + 1 = P.parts.card := by
  change (P.replace _ _ _ _ _ _ _ _).parts.card + 1 = _
  erw [P.replace_card]
  have hc : 2 ≤ P.parts.card := by
    have := card_le_card (show ({S,T}:Finset _) ⊆ P.parts by
      intro U hU
      rcases mem_insert.mp hU with rfl | hU
      · exact hS
      · exact mem_singleton.mp hU ▸ hT)
    simpa [hST] using this
  simp [hST]
  omega

@[simp] theorem merge_core (P : Decomposition n) {S T : Finset (Fin n)}
    (hS : S ∈ P.parts) (hT : T ∈ P.parts) (hST : S ≠ T) :
    (P.merge hS hT hST).core = P.core := by
  ext v
  simp only [mem_core,merge_parts,mem_union,mem_sdiff,mem_insert,mem_singleton]
  constructor
  · rintro ⟨U, hU, hvU⟩
    rcases hU with ⟨hU,_⟩ | rfl
    · exact ⟨U,hU,hvU⟩
    · rcases mem_union.mp hvU with hv | hv
      · exact ⟨S,hS,hv⟩
      · exact ⟨T,hT,hv⟩
  · rintro ⟨U,hU,hvU⟩
    by_cases heS : U=S
    · subst U; exact ⟨S∪T,Or.inr rfl,mem_union_left _ hvU⟩
    by_cases heT : U=T
    · subst U; exact ⟨S∪T,Or.inr rfl,mem_union_right _ hvU⟩
    exact ⟨U,Or.inl ⟨hU,not_or.mpr ⟨heS,heT⟩⟩,hvU⟩

noncomputable def absorb (P : Decomposition n) {S : Finset (Fin n)} {v : Fin n}
    (hS : S ∈ P.parts) (hv : v ∈ P.Y) : Decomposition n := by
  classical
  have hvc : v ∉ P.core := fun h => disjoint_left.mp P.core_disjoint_Y h hv
  have hvS : v ∉ S := fun h => hvc (P.subset_core hS h)
  have hcore : ((insert (insert v S) (P.parts.erase S)).biUnion id) = insert v P.core := by
    ext w
    simp only [mem_biUnion,mem_insert,mem_erase,id_eq]
    constructor
    · rintro ⟨U, rfl | hU, hw⟩
      · rcases mem_insert.mp hw with rfl | hw
        · exact Or.inl rfl
        · exact Or.inr (P.subset_core hS hw)
      · exact Or.inr ((P.mem_core w).2 ⟨U,hU.2,hw⟩)
    · intro hw
      rcases hw with he | hw
      · subst w
        exact ⟨insert v S,Or.inl rfl,mem_insert_self _ _⟩
      · obtain ⟨U,hU,hwU⟩ := (P.mem_core w).1 hw
        by_cases he : U=S
        · subst U; exact ⟨insert v S,Or.inl rfl,mem_insert_of_mem hwU⟩
        · exact ⟨U,Or.inr ⟨he,hU⟩,hwU⟩
  refine { parts := insert (insert v S) (P.parts.erase S), X := P.X, Y := P.Y.erase v
           nonempty := ?_, pairwise := ?_, disjoint_X := ?_, disjoint_Y := ?_,
           disjoint_XY := P.disjoint_XY.mono_right (erase_subset _ _), cover := ?_ }
  · intro U hU
    rcases mem_insert.mp hU with rfl | hU
    · exact ⟨v,mem_insert_self _ _⟩
    · exact P.nonempty U (mem_erase.mp hU).2
  · intro U hU W hW hUW
    simp only [mem_coe,mem_insert,mem_erase] at hU hW
    have cross : ∀ T ∈ P.parts, T ≠ S → Disjoint (insert v S) T := by
      intro T hT hTS
      rw [disjoint_insert_left]
      exact ⟨fun hvT => hvc (P.subset_core hT hvT),P.pairwise hS hT hTS.symm⟩
    rcases hU with rfl | hU <;> rcases hW with rfl | hW
    · exact (hUW rfl).elim
    · exact cross W hW.2 hW.1
    · exact (cross U hU.2 hU.1).symm
    · exact P.pairwise hU.2 hW.2 hUW
  · intro U hU
    rcases mem_insert.mp hU with rfl | hU
    · rw [disjoint_insert_left]
      exact ⟨fun hvX => disjoint_left.mp P.disjoint_XY hvX hv,P.disjoint_X S hS⟩
    · exact P.disjoint_X U (mem_erase.mp hU).2
  · intro U hU
    rcases mem_insert.mp hU with rfl | hU
    · rw [disjoint_insert_left]
      refine ⟨by simp, (P.disjoint_Y S hS).mono_right (erase_subset _ _)⟩
    · exact (P.disjoint_Y U (mem_erase.mp hU).2).mono_right (erase_subset _ _)
  · rw [hcore]
    ext w
    have hc : w ∈ P.core ∪ P.X ∪ P.Y := by change w ∈ P.parts.biUnion id ∪ P.X ∪ P.Y; rw[P.cover]; simp
    simp only [mem_union,mem_insert,mem_erase,mem_univ] at *
    constructor
    · intro _; trivial
    · intro _
      by_cases he : w=v
      · exact Or.inl (Or.inl (Or.inl he))
      rcases hc with (hc | hx) | hy
      · exact Or.inl (Or.inl (Or.inr hc))
      · exact Or.inl (Or.inr hx)
      · exact Or.inr ⟨he,hy⟩

@[simp] theorem absorb_parts (P : Decomposition n) {S : Finset (Fin n)} {v : Fin n}
    (hS : S ∈ P.parts) (hv : v ∈ P.Y) :
    (P.absorb hS hv).parts = insert (insert v S) (P.parts.erase S) := rfl

@[simp] theorem absorb_X (P : Decomposition n) {S : Finset (Fin n)} {v : Fin n}
    (hS : S ∈ P.parts) (hv : v ∈ P.Y) : (P.absorb hS hv).X = P.X := rfl

@[simp] theorem absorb_Y (P : Decomposition n) {S : Finset (Fin n)} {v : Fin n}
    (hS : S ∈ P.parts) (hv : v ∈ P.Y) : (P.absorb hS hv).Y = P.Y.erase v := rfl

@[simp] theorem absorb_card (P : Decomposition n) {S : Finset (Fin n)} {v : Fin n}
    (hS : S ∈ P.parts) (hv : v ∈ P.Y) : (P.absorb hS hv).parts.card = P.parts.card := by
  rw [absorb_parts,card_insert_of_notMem,card_erase_of_mem hS]
  · have hc := card_pos.mpr (show P.parts.Nonempty from ⟨S,hS⟩)
    omega
  · intro h
    exact disjoint_left.mp (P.disjoint_Y _ (mem_erase.mp h).2) (mem_insert_self _ _) hv

@[simp] theorem absorb_core (P : Decomposition n) {S : Finset (Fin n)} {v : Fin n}
    (hS : S ∈ P.parts) (hv : v ∈ P.Y) : (P.absorb hS hv).core = insert v P.core := by
  change (insert (insert v S) (P.parts.erase S)).biUnion id = _
  rw [biUnion_insert,id_eq]
  have hh : S ∪ (P.parts.erase S).biUnion id = P.core := by
    calc
      S ∪ (P.parts.erase S).biUnion id = (insert S (P.parts.erase S)).biUnion id := by simp only [biUnion_insert,id_eq]
      _ = P.core := by rw [insert_erase hS]; rfl
  rw [insert_union,hh]


noncomputable def trim (P : Decomposition n) (D : Finset (Fin n) → Finset (Fin n))
    (hD : ∀ S ∈ P.parts, D S ⊆ S)
    (hne : ∀ S ∈ P.parts, (S \ D S).Nonempty) : Decomposition n :=
  P.replace P.parts (P.parts.image (fun S => S \ D S)) (P.parts.biUnion D)
    subset_rfl (by
      intro T hT
      obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
      exact hne S hS) (by
      intro T hT U hU hTU
      obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
      obtain ⟨W,hW,rfl⟩ := mem_image.mp hU
      exact (P.pairwise hS hW (fun he => hTU (he ▸ rfl))).mono
        sdiff_subset sdiff_subset) (by
      ext v
      simp only [mem_union,mem_biUnion,mem_image,id_eq]
      constructor
      · rintro (⟨T,⟨S,hS,rfl⟩,hv⟩ | ⟨S,hS,hv⟩)
        · exact ⟨S,hS,(mem_sdiff.mp hv).1⟩
        · exact ⟨S,hS,hD S hS hv⟩
      · rintro ⟨S,hS,hv⟩
        by_cases hvD : v ∈ D S
        · exact Or.inr ⟨S,hS,hvD⟩
        · exact Or.inl ⟨S \ D S,⟨S,hS,rfl⟩,mem_sdiff.mpr ⟨hv,hvD⟩⟩) (by
      rw [disjoint_left]
      intro v hv hd
      obtain ⟨T,hT,hvT⟩ := mem_biUnion.mp hv
      obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
      obtain ⟨W,hW,hvW⟩ := mem_biUnion.mp hd
      by_cases he : S=W
      · subst W
        exact (mem_sdiff.mp hvT).2 hvW
      · exact disjoint_left.mp (P.pairwise hS hW he)
          (mem_sdiff.mp hvT).1 (hD W hW hvW))

@[simp] theorem trim_parts (P : Decomposition n) (D : Finset (Fin n) → Finset (Fin n))
    (hD : ∀ S ∈ P.parts, D S ⊆ S)
    (hne : ∀ S ∈ P.parts, (S \ D S).Nonempty) :
    (P.trim D hD hne).parts = P.parts.image (fun S => S \ D S) := by
  simp [trim,replace]

@[simp] theorem trim_X (P : Decomposition n) (D : Finset (Fin n) → Finset (Fin n))
    (hD : ∀ S ∈ P.parts, D S ⊆ S)
    (hne : ∀ S ∈ P.parts, (S \ D S).Nonempty) :
    (P.trim D hD hne).X = P.X ∪ P.parts.biUnion D := rfl

@[simp] theorem trim_Y (P : Decomposition n) (D : Finset (Fin n) → Finset (Fin n))
    (hD : ∀ S ∈ P.parts, D S ⊆ S)
    (hne : ∀ S ∈ P.parts, (S \ D S).Nonempty) :
    (P.trim D hD hne).Y = P.Y := rfl

@[simp] theorem trim_card (P : Decomposition n) (D : Finset (Fin n) → Finset (Fin n))
    (hD : ∀ S ∈ P.parts, D S ⊆ S)
    (hne : ∀ S ∈ P.parts, (S \ D S).Nonempty) :
    (P.trim D hD hne).parts.card = P.parts.card := by
  rw [trim_parts]
  apply card_image_iff.mpr
  intro S hS T hT he
  by_contra hST
  obtain ⟨v,hv⟩ := hne S hS
  have hvT : v ∈ T \ D T := by
    change S \ D S = T \ D T at he
    rw [←he]
    exact hv
  exact disjoint_left.mp (P.pairwise hS hT hST)
    (mem_sdiff.mp hv).1 (mem_sdiff.mp hvT).1

 theorem trim_core_subset (P : Decomposition n) (D : Finset (Fin n) → Finset (Fin n))
    (hD : ∀ S ∈ P.parts, D S ⊆ S)
    (hne : ∀ S ∈ P.parts, (S \ D S).Nonempty) :
    (P.trim D hD hne).core ⊆ P.core := by
  intro v hv
  obtain ⟨T,hT,hvT⟩ := (mem_core _ v).mp hv
  rw [trim_parts] at hT
  obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
  exact P.subset_core hS (mem_sdiff.mp hvT).1

end Decomposition
end HadwigerRamsey.ControlledPartition
