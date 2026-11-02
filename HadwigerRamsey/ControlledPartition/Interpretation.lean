import HadwigerRamsey.ControlledPartition.Decomposition
import HadwigerRamsey.ThomasonUpper.Connectivity

open Finset
open scoped Classical

namespace HadwigerRamsey.ControlledPartition

/-- The finite-set deletion definition is the usual integer-valued vertex
connectivity, with real thresholds interpreted by taking their ceiling. -/
theorem realConnected_univ_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (t : ℝ) :
    RealConnected G univ t ↔ t ≤ (ThomasonUpper.vertexConnectivity G : ℝ) := by
  have hn1 : 1 ≤ n := hn
  have hpred : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  rw [← Nat.ceil_le, ← ThomasonUpper.vertexConnectedAtLeast_iff hn]
  constructor
  · intro h
    have hc : ⌈t⌉₊ ≤ n-1 := Nat.ceil_le.mpr (by simpa only [card_univ,Fintype.card_fin,hpred] using h.1)
    refine ⟨by omega, ?_⟩
    intro Z hZ
    have hh := h.2 Z (subset_univ _) (Nat.lt_ceil.mp hZ)
    convert hh using 1 <;> congr 1 <;> ext v <;> simp
  · intro h
    refine ⟨?_, ?_⟩
    · have hc : ⌈t⌉₊ ≤ n-1 := by have hh := h.1; omega
      have ht := Nat.le_ceil t
      have hcR : (⌈t⌉₊ : ℝ) ≤ (n-1 : ℕ) := by exact_mod_cast hc
      simpa only [card_univ,Fintype.card_fin,hpred] using ht.trans hcR
    · intro Z _ hZ
      have hh := h.2 Z (Nat.lt_ceil.mpr hZ)
      convert hh using 1 <;> congr 1 <;> ext v <;> simp

noncomputable def imageInduceIso {m n : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin m → Fin n) (hf : Function.Injective f) (D : Finset (Fin m)) :
    ((G.comap f).induce (↑D : Set (Fin m))) ≃g
      G.induce (↑(D.image f) : Set (Fin n)) where
  toEquiv := Equiv.ofBijective
    (fun x => ⟨f x.val,mem_image.mpr ⟨x.val,x.property,rfl⟩⟩)
    ⟨by
      intro x y hxy
      exact Subtype.ext (hf (congrArg Subtype.val hxy)),by
      rintro ⟨v,hv⟩
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
      exact ⟨⟨u,hu⟩,rfl⟩⟩
  map_rel_iff' := by intro x y; rfl

theorem realConnected_image_iff {m n : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin m → Fin n) (hf : Function.Injective f) (D : Finset (Fin m)) (t : ℝ) :
    RealConnected (G.comap f) D t ↔ RealConnected G (D.image f) t := by
  constructor
  · intro h
    refine ⟨by simpa only [card_image_of_injective D hf] using h.1, ?_⟩
    intro Z hZD hZ
    let W := D.filter (fun v => f v ∈ Z)
    have hWD : W ⊆ D := filter_subset _ _
    have hW : W.image f = Z := by
      ext v
      constructor
      · intro hv
        obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
        exact (mem_filter.mp hw).2
      · intro hv
        obtain ⟨w,hw,rfl⟩ := mem_image.mp (hZD hv)
        exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
    have hc : W.card = Z.card := by
      rw [←hW,card_image_of_injective W hf]
    have hC := h.2 W hWD (by simpa only [hc] using hZ)
    have hh := (imageInduceIso G f hf (D \ W)).connected_iff.mp hC
    convert hh using 1 <;> congr 1 <;>
      exact congrArg (fun U : Finset (Fin n) => (U : Set (Fin n))) (by rw [image_sdiff D W hf,hW])
  · intro h
    refine ⟨by simpa only [card_image_of_injective D hf] using h.1, ?_⟩
    intro Z hZD hZ
    have hi : Z.image f ⊆ D.image f := image_subset_image hZD
    have hc : ((Z.image f).card : ℝ) < t := by
      simpa only [card_image_of_injective Z hf] using hZ
    have hh := h.2 (Z.image f) hi hc
    apply (imageInduceIso G f hf (D \ Z)).connected_iff.mpr
    convert hh using 1 <;> congr 1 <;>
      exact congrArg (fun U : Finset (Fin n) => (U : Set (Fin n))) (image_sdiff D Z hf)

/-- The graph induced on a finite set, enumerated by its own cardinality. -/
noncomputable def inducedGraph {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : SimpleGraph (Fin S.card) :=
  G.comap (fun i => (S.equivFin.symm i).val)

/-- An explicit compatibility theorem with the connectivity used in Theorem 1.5. -/
theorem realConnected_iff_vertexConnectivity {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : S.Nonempty) (t : ℝ) :
    RealConnected G S t ↔
      t ≤ (ThomasonUpper.vertexConnectivity (inducedGraph G S) : ℝ) := by
  let f : Fin S.card → Fin n := fun i => (S.equivFin.symm i).val
  have hf : Function.Injective f := by
    intro i j hij
    exact S.equivFin.symm.injective (Subtype.ext hij)
  have hr : (univ : Finset (Fin S.card)).image f = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact (S.equivFin.symm i).property
    · intro hv
      exact mem_image.mpr ⟨S.equivFin ⟨v,hv⟩,mem_univ _,by simp [f]⟩
  have he := realConnected_image_iff G f hf univ t
  rw [hr] at he
  exact he.symm.trans (realConnected_univ_iff (inducedGraph G S) hS.card_pos t)

/-- The bound on the number of connected pieces recorded after the definition. -/
theorem Controlled.card_parts_le {n : ℕ} {G : SimpleGraph (Fin n)}
    {ε η δ : ℝ} {P : Decomposition n} (h : Controlled G ε η δ P)
    (hn : 0 < n) (hε : 0 < ε) : (P.parts.card : ℝ) ≤ ε⁻¹ := by
  have hs : (P.parts.card : ℝ) * (ε*n) ≤ n := by
    calc
      _ = ∑ _S ∈ P.parts, ε*n := by simp
      _ ≤ ∑ S ∈ P.parts, (S.card : ℝ) := sum_le_sum h.2.2.2.2.1
      _ ≤ n := by exact_mod_cast P.sum_card_parts_le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (P.parts.card : ℝ)*ε ≤ 1 := by nlinarith only [hs,hnR]
  rw [inv_eq_one_div]
  exact (le_div_iff₀ hε).mpr hm

end HadwigerRamsey.ControlledPartition
