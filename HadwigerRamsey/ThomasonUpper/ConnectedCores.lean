import HadwigerRamsey.ThomasonUpper.PathAllocation
import HadwigerRamsey.ThomasonUpper.BranchSets

open scoped BigOperators
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Build disjoint connected cores from disjoint nonempty subsets of D,
using globally disjoint short-path interiors in C. A star with a chosen
root replaces the manuscript's consecutive-pair chain, with the same
upper bound on the number of requested paths. -/
theorem connected_reservoir_cores {n m H L : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin m → Finset (Fin n)) (C D : Finset (Fin n)) {T : ℝ}
    (hM : ∀ a, (M a).Nonempty) (hMD : ∀ a, M a ⊆ D)
    (hML : ∀ a, (M a).card ≤ L)
    (hMdisj : ∀ a b, a ≠ b → Disjoint (M a) (M b)) (hCD : Disjoint C D)
    (hbudget : ((H-1)*(m*L) : ℕ) < T)
    (hpaths : ∀ u ∈ D, ∀ v ∈ D, u ≠ v →
      ∃ P : Finset (G.Path u v), T ≤ (P.card : ℝ) ∧
        (∀ p ∈ P, p.val.length ≤ H ∧ pathInterior p ⊆ C) ∧
        (P : Set (G.Path u v)).PairwiseDisjoint pathInterior) :
    ∃ K : Fin m → Set (Fin n),
      (∀ a, (M a : Set (Fin n)) ⊆ K a ∧ (G.induce (K a)).Connected ∧
        K a ⊆ (M a : Set (Fin n)) ∪ (C : Set (Fin n))) ∧
      ∀ a b, a ≠ b → Disjoint (K a) (K b) := by
  classical
  choose root hroot using hM
  let J := Σ a : Fin m, {v : M a // v.val ≠ root a}
  have hJ : Fintype.card J ≤ m*L := by
    calc
      _ = ∑ a, Fintype.card {v : M a // v.val ≠ root a} := Fintype.card_sigma
      _ ≤ ∑ a, (M a).card := sum_le_sum fun a _ => by
        have hh := Fintype.card_le_of_injective (fun v : {v : M a // v.val ≠ root a} => v.val)
          Subtype.val_injective
        simpa only [Fintype.card_coe] using hh
      _ ≤ ∑ _a : Fin m, L := sum_le_sum fun a _ => hML a
      _ = m*L := by simp
  have hPs : ∀ j : J, ∃ P : Finset (G.Path (root j.fst) j.snd.val.val),
      T ≤ (P.card : ℝ) ∧ (∀ p ∈ P, p.val.length ≤ H ∧ pathInterior p ⊆ C) ∧
      (P : Set (G.Path (root j.fst) j.snd.val.val)).PairwiseDisjoint pathInterior := by
    intro j
    exact hpaths _ (hMD _ (hroot _)) _ (hMD _ j.snd.val.property) j.snd.property.symm
  choose P hPcard hP hPdisj using hPs
  obtain ⟨p, hp, hpC, hpdisj⟩ := allocate_path_interiors
    (fun j : J => root j.fst) (fun j : J => j.snd.val.val)
    (fun j => j.snd.property.symm) C H P hPdisj
    (fun j q hq => (hP j q hq).2) (fun j q hq => (hP j q hq).1) (by
      intro j
      have hh : Fintype.card J*(H-1) ≤ (H-1)*(m*L) := by nlinarith
      have hhR : (Fintype.card J*(H-1) : ℕ) < T :=
        lt_of_le_of_lt (by exact_mod_cast hh) hbudget
      exact_mod_cast hhR.trans_le (hPcard j))
  let w := fun a (v : M a) =>
    if h : v.val = root a then (SimpleGraph.Walk.nil : G.Walk (root a) (root a)).copy rfl h.symm
    else (p ⟨a,⟨v,h⟩⟩).val
  let K := fun a => {x | ∃ v : M a, x ∈ (w a v).support}
  have hnon : ∀ a, Nonempty (M a) := fun a => ⟨⟨root a,hroot a⟩⟩
  have hinterior : ∀ a (v : M a) x, x ∈ (w a v).support →
      x ∉ M a → ∃ h : v.val ≠ root a, x ∈ pathInterior (p ⟨a,⟨v,h⟩⟩) := by
    intro a v x hx hxM
    by_cases hv : v.val = root a
    · simp only [w, dif_pos hv, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil,
        List.mem_singleton] at hx
      exact False.elim (hxM (hx ▸ hroot a))
    · refine ⟨hv, mem_sdiff.mpr ⟨List.mem_toFinset.mpr ?_, ?_⟩⟩
      · simpa only [w, dif_neg hv] using hx
      · intro he
        rcases mem_insert.mp he with he | he
        · exact hxM (he ▸ hroot a)
        · exact hxM ((mem_singleton.mp he) ▸ v.property)
  have hKC : ∀ a, K a ⊆ (M a : Set (Fin n)) ∪ (C : Set (Fin n)) := by
    intro a x hx
    by_cases hxM : x ∈ M a
    · exact Or.inl hxM
    · obtain ⟨v,hv⟩ := hx
      obtain ⟨h,hi⟩ := hinterior a v x hv hxM
      exact Or.inr (hpC _ hi)
  refine ⟨K, ?_, ?_⟩
  · intro a
    refine ⟨?_, ?_, hKC a⟩
    · intro v hv
      exact ⟨⟨v,hv⟩, (w a ⟨v,hv⟩).end_mem_support⟩
    · letI : Nonempty (M a) := hnon a
      exact connected_walk_union (fun v : M a => v.val) (w a)
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have hxb' := hKC b hxb
    have hxa' := hKC a hxa
    by_cases hxaM : x ∈ M a
    · rcases hxb' with hxbM | hxbC
      · exact Finset.disjoint_left.mp (hMdisj a b hab) hxaM hxbM
      · exact Finset.disjoint_left.mp hCD hxbC (hMD a hxaM)
    · by_cases hxbM : x ∈ M b
      · exact Finset.disjoint_left.mp hCD (hxa'.resolve_left hxaM) (hMD b hxbM)
      · obtain ⟨v,hv⟩ := hxa
        obtain ⟨z,hz⟩ := hxb
        obtain ⟨hv',hvi⟩ := hinterior a v x hv hxaM
        obtain ⟨hz',hzi⟩ := hinterior b z x hz hxbM
        have hne : (⟨a,⟨v,hv'⟩⟩ : J) ≠ ⟨b,⟨z,hz'⟩⟩ := fun h => hab (congrArg Sigma.fst h)
        exact Finset.disjoint_left.mp (hpdisj _ _ hne) hvi hzi

end HadwigerRamsey.ThomasonUpper
