import HadwigerRamsey.Blocks

open scoped BigOperators Classical
open Finset HadwigerRamsey

namespace ComponentTransfer.Construction

noncomputable def componentSet {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) : Finset (Fin n) :=
  univ.filter (fun v => label (τ v) = t)

noncomputable def componentSize {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) : ℕ := (componentSet τ label t).card

noncomputable def componentMap {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) : Fin (componentSize τ label t) → Fin n :=
  (componentSet τ label t).orderEmbOfFin rfl

lemma componentMap_strictMono {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) : StrictMono (componentMap τ label t) :=
  ((componentSet τ label t).orderEmbOfFin rfl).strictMono

lemma componentMap_label {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) (v : Fin (componentSize τ label t)) :
    label (τ (componentMap τ label t v)) = t := by
  exact (mem_filter.mp ((componentSet τ label t).orderEmbOfFin_mem rfl v)).2

lemma componentMap_cover {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) (v : Fin n) (hv : label (τ v) = t) :
    v ∈ Set.range (componentMap τ label t) := by
  change v ∈ Set.range ((componentSet τ label t).orderEmbOfFin rfl)
  rw [range_orderEmbOfFin]
  exact mem_filter.mpr ⟨mem_univ _, hv⟩

lemma component_class_card {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t i : Fin k) :
    (univ.filter (fun v => τ (componentMap τ label t v) = i)).card =
      if label i = t then (univ.filter (fun v => τ v = i)).card else 0 := by
  by_cases hi : label i = t
  · rw [if_pos hi]
    apply card_bij (fun v _ => componentMap τ label t v)
    · intro v hv
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩
    · intro v hv w hw he
      exact (componentMap_strictMono τ label t).injective he
    · intro v hv
      have hvi := (mem_filter.mp hv).2
      obtain ⟨w, hw⟩ := componentMap_cover τ label t v (by rw [hvi]; exact hi)
      exact ⟨w, mem_filter.mpr ⟨mem_univ _, by rw [hw]; exact hvi⟩, hw⟩
  · rw [if_neg hi]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hc := componentMap_label τ label t v
    rw [(mem_filter.mp hv).2] at hc
    exact hi hc

lemma component_classMass {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t i : Fin k) :
    classMass (τ ∘ componentMap τ label t) i =
      if label i = t then
        ((univ.filter (fun v => τ v = i)).card : ℝ) / componentSize τ label t else 0 := by
  unfold classMass
  change ((univ.filter (fun v => τ (componentMap τ label t v) = i)).card : ℝ) / _ = _
  rw [component_class_card]
  split_ifs <;> simp

lemma componentSize_eq_sum {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) :
    componentSize τ label t =
      ∑ i with label i = t, (univ.filter (fun v => τ v = i)).card := by
  symm
  simpa [componentSize, componentSet] using
    sum_card_fiberwise_eq_card_filter (univ : Finset (Fin n))
      (univ.filter (fun i => label i = t)) τ

lemma componentSize_ratio {n k : ℕ} (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t : Fin k) :
    (componentSize τ label t : ℝ) / n = ∑ i with label i = t, classMass τ i := by
  rw [componentSize_eq_sum, Nat.cast_sum, Finset.sum_div]
  rfl

lemma component_classMass_ratio {n k : ℕ} (hn : 0 < n) (τ : Fin n → Fin k)
    (label : Fin k → Fin k) (t i : Fin k) :
    classMass (τ ∘ componentMap τ label t) i =
      if label i = t then classMass τ i / ((componentSize τ label t : ℝ) / n) else 0 := by
  rw [component_classMass]
  split_ifs
  · unfold classMass
    rw [div_div_div_cancel_right₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  · rfl

end ComponentTransfer.Construction
