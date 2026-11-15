import Mathlib

open scoped BigOperators
open Finset

namespace HadwigerRamsey

/-- A clique minor given by disjoint, nonempty, connected branch sets. -/
def HasCliqueMinor {V : Type*} (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∃ B : Fin s → Set V,
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- A partition is represented by its vertex-to-part map. Surjectivity is
unnecessary for the upper bound and is deliberately not required. -/
def Permissible {V : Type*} (G : SimpleGraph V) {s : ℕ} (f : V → Fin s) : Prop :=
  ∀ i j, i ≠ j → ∃ u v, f u = i ∧ f v = j ∧ G.Adj u v

theorem HasCliqueMinor.mono {V : Type*} {G : SimpleGraph V} {s t : ℕ}
    (h : HasCliqueMinor G t) (hst : s ≤ t) : HasCliqueMinor G s := by
  obtain ⟨B, hc, hd, he⟩ := h
  let e := Fin.castLEEmb hst
  exact ⟨B ∘ e, fun i => hc (e i), fun i j hij => hd _ _ (e.injective.ne hij),
    fun i j hij => he _ _ (e.injective.ne hij)⟩

/-- The minor-to-partition step in Lemma B.1. -/
theorem HasCliqueMinor.permissible {V : Type*} {G : SimpleGraph V} {s : ℕ}
    (h : HasCliqueMinor G s) (hs : 0 < s) : ∃ f : V → Fin s, Permissible G f := by
  classical
  obtain ⟨B, hc, hd, he⟩ := h
  let f : V → Fin s := fun v => if h : ∃ i, v ∈ B i then h.choose else ⟨0, hs⟩
  have hf : ∀ i v, v ∈ B i → f v = i := by
    intro i v hv
    have hex : ∃ j, v ∈ B j := ⟨i, hv⟩
    dsimp [f]
    rw [dif_pos hex]
    by_contra hne
    exact Set.disjoint_left.mp (hd _ _ hne) hex.choose_spec hv
  refine ⟨f, fun i j hij => ?_⟩
  obtain ⟨u, hu, v, hv, huv⟩ := he i j hij
  exact ⟨u, v, hf i u hu, hf j v hv, huv⟩

/-- Unordered potential edges, represented by increasing ordered pairs. -/
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

/-- The block pair containing an edge, when its endpoints have distinct labels. -/
abbrev Crosses {n s : ℕ} (f : Fin n → Fin s) (a : Edge s) (e : Edge n) : Prop :=
  (f e.val.1 = a.val.1 ∧ f e.val.2 = a.val.2) ∨
  (f e.val.1 = a.val.2 ∧ f e.val.2 = a.val.1)

theorem crosses_disjoint {n s : ℕ} (f : Fin n → Fin s) {a b : Edge s}
    (hab : a ≠ b) : Disjoint {e | Crosses f a e} {e | Crosses f b e} := by
  rw [Set.disjoint_left]
  intro e ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · apply hab; apply Subtype.ext; exact Prod.ext (ha.1.symm.trans hb.1) (ha.2.symm.trans hb.2)
  · have := a.property; have := b.property; omega
  · have := a.property; have := b.property; omega
  · apply hab; apply Subtype.ext; exact Prod.ext (ha.2.symm.trans hb.2) (ha.1.symm.trans hb.1)

/-- Permissibility is a conjunction of independent block-pair hit events. -/
theorem permissible_iff_crosses {n s : ℕ} (G : SimpleGraph (Fin n)) (f : Fin n → Fin s) :
    Permissible G f ↔ ∀ a : Edge s, ∃ e : Edge n, Crosses f a e ∧ G.Adj e.val.1 e.val.2 := by
  constructor
  · intro h a
    obtain ⟨u, v, hu, hv, huv⟩ := h a.val.1 a.val.2 (ne_of_lt a.property)
    rcases lt_or_gt_of_ne (G.ne_of_adj huv) with hlt | hgt
    · exact ⟨⟨(u,v), hlt⟩, Or.inl ⟨hu,hv⟩, huv⟩
    · exact ⟨⟨(v,u), hgt⟩, Or.inr ⟨hv,hu⟩, huv.symm⟩
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨e, he, hg⟩ := h ⟨(i,j), hlt⟩
      rcases he with he | he
      · exact ⟨e.val.1, e.val.2, he.1, he.2, hg⟩
      · exact ⟨e.val.2, e.val.1, he.2, he.1, hg.symm⟩
    · obtain ⟨e, he, hg⟩ := h ⟨(j,i), hgt⟩
      rcases he with he | he
      · exact ⟨e.val.2, e.val.1, he.2, he.1, hg.symm⟩
      · exact ⟨e.val.1, e.val.2, he.1, he.2, hg⟩

theorem HasCliqueMinor.card_le {n s : ℕ} {G : SimpleGraph (Fin n)}
    (h : HasCliqueMinor G s) : s ≤ n := by
  classical
  obtain ⟨B, hc, hd, he⟩ := h
  let v : Fin s → Fin n := fun i => (hc i).nonempty.some.val
  have hv : ∀ i, v i ∈ B i := fun i => (hc i).nonempty.some.property
  have hinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (hd i j hne) (hv i) (hij.symm ▸ hv j)
  simpa using Fintype.card_le_of_injective v hinj

/-- The largest order of a clique minor; order zero is allowed for the empty graph. -/
noncomputable def hadwigerNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (univ.filter (fun s : Fin (n+1) => HasCliqueMinor G s)).sup (fun s => s.val)

theorem cliqueMinor_le_hadwigerNumber {n s : ℕ} {G : SimpleGraph (Fin n)}
    (h : HasCliqueMinor G s) : s ≤ hadwigerNumber G := by
  classical
  exact Finset.le_sup (f := fun s : Fin (n+1) => s.val)
    (mem_filter.mpr ⟨mem_univ _, h⟩ : (⟨s, by have := h.card_le; omega⟩ : Fin (n+1)) ∈ _)

lemma hadwigerNumber_lt_of_no_minor {n s : ℕ} {G : SimpleGraph (Fin n)}
    (hs : 0 < s) (h : ¬HasCliqueMinor G s) : hadwigerNumber G < s := by
  classical
  have hle : hadwigerNumber G ≤ s-1 := by
    apply Finset.sup_le
    intro t ht
    have ht' := (mem_filter.mp ht).2
    by_contra hn
    have hst : s ≤ (t : ℕ) := by omega
    exact h (ht'.mono hst)
  omega

/-- The supremum in the definition is attained by an actual clique minor. -/
theorem hadwigerNumber_hasCliqueMinor {n : ℕ} (G : SimpleGraph (Fin n)) :
    HasCliqueMinor G (hadwigerNumber G) := by
  classical
  have hzero : HasCliqueMinor G 0 := by
    refine ⟨Fin.elim0, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i
  let S := univ.filter (fun s : Fin (n+1) => HasCliqueMinor G s)
  have hS : S.Nonempty := ⟨⟨0, by omega⟩, mem_filter.mpr ⟨mem_univ _, hzero⟩⟩
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup S hS (fun s => s.val)
  change HasCliqueMinor G (S.sup (fun s => s.val))
  rw [heq]
  exact (mem_filter.mp hs).2

/-- This identifies the defined Hadwiger number with the usual maximum minor order. -/
theorem hasCliqueMinor_iff_le_hadwigerNumber {n s : ℕ} (G : SimpleGraph (Fin n)) :
    HasCliqueMinor G s ↔ s ≤ hadwigerNumber G :=
  ⟨cliqueMinor_le_hadwigerNumber, fun h => (hadwigerNumber_hasCliqueMinor G).mono h⟩

end HadwigerRamsey
