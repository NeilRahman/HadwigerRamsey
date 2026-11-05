import ComponentTransfer.LiftingStability
import HadwigerRamsey.ThomasonUpper.Restriction

open scoped BigOperators Classical
open Finset Real
open HadwigerRamsey HadwigerRamsey.ThomasonUpper HadwigerRamsey.Main
open HadwigerRamsey.ControlledPartition

namespace ComponentTransfer.Lifting

noncomputable def retainedClasses {m k : ℕ} (τ : Fin m → Fin k)
    (P : Finset (Fin m)) : Fin P.card → Fin k :=
  fun v => τ (P.equivFin.symm v).val

lemma retained_class_image {m k : ℕ} (τ : Fin m → Fin k)
    (P : Finset (Fin m)) (i : Fin k) :
    (classVertices (retainedClasses τ P) i).image (fun v => (P.equivFin.symm v).val) =
      classVertices τ i ∩ P := by
  ext v
  simp only [Finset.mem_image, classVertices, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter, retainedClasses]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(Finset.mem_filter.mp hw).2,(P.equivFin.symm w).property⟩
  · rintro ⟨hi,hP⟩
    refine ⟨P.equivFin ⟨v,hP⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa using hi⟩
    · simp

lemma retainedClassMass {m k : ℕ} (τ : Fin m → Fin k)
    (P : Finset (Fin m)) (i : Fin k) :
    classMass (retainedClasses τ P) i = ((classVertices τ i ∩ P).card : ℝ)/P.card := by
  have hc := congrArg Finset.card (retained_class_image τ P i)
  have hf : Function.Injective (fun v : Fin P.card => (P.equivFin.symm v).val) := by
    intro i j hij
    exact P.equivFin.symm.injective (Subtype.ext hij)
  rw [Finset.card_image_of_injective _ hf] at hc
  change ((classVertices (retainedClasses τ P) i).card : ℝ)/P.card = _
  rw [hc]

lemma retained_class_eq_deleted {m k : ℕ} (τ : Fin m → Fin k)
    (P : Finset (Fin m)) (i : Fin k) :
    classVertices τ i ∩ P = classVertices τ i \ (univ \ P) := by
  ext v
  simp

attribute [-instance] SimpleGraph.instDecidableComapAdj in
lemma retainedBlockDensity {m k : ℕ} (G : SimpleGraph (Fin m)) (τ : Fin m → Fin k)
    (P : Finset (Fin m)) (i j : Fin k) :
    blockDensity (inducedGraph G P) (retainedClasses τ P) i j =
      deletedBlockDensity G τ (univ \ P) i j := by
  have hf : Function.Injective (fun v : Fin P.card => (P.equivFin.symm v).val) := by
    intro i j hij
    exact P.equivFin.symm.injective (Subtype.ext hij)
  unfold blockDensity deletedBlockDensity inducedGraph
  split
  · exact (internalDensity_comap G _ hf _).trans
      (congrArg (internalDensity G) ((retained_class_image τ P i).trans (retained_class_eq_deleted τ P i)))
  · exact congrArg (fun q : ℚ => (q : ℝ))
      ((edgeDensity_comap G _ hf _ _).trans
        (congrArg₂ G.edgeDensity
          ((retained_class_image τ P i).trans (retained_class_eq_deleted τ P i))
          ((retained_class_image τ P j).trans (retained_class_eq_deleted τ P j))))

/-- Ambiently normalized retained class counts. -/
noncomputable def retainedMass {m k : ℕ} (n : ℕ) (τ : Fin m → Fin k)
    (P : Finset (Fin m)) (i : Fin k) : ℝ :=
  ((classVertices τ i ∩ P).card : ℝ)/(n : ℝ)

lemma retainedMass_bounds {n m k : ℕ} (hmn : m ≤ n) (τ : Fin m → Fin k)
    (P : Finset (Fin m)) (i : Fin k) : retainedMass n τ P i ∈ Set.Icc (0 : ℝ) 1 := by
  have hc : (classVertices τ i ∩ P).card ≤ n :=
    (Finset.card_le_card Finset.inter_subset_left).trans
      ((by simpa using (classVertices τ i).card_le_univ : (classVertices τ i).card ≤ m).trans hmn)
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · exact div_le_one_of_le₀ (by exact_mod_cast hc) (by positivity)

lemma retainedMass_scale {n m k : ℕ} (hn : 0 < n) (τ : Fin m → Fin k)
    (P : Finset (Fin m)) (i : Fin k) :
    (n : ℝ)/P.card*retainedMass n τ P i = classMass (retainedClasses τ P) i := by
  rw [retainedClassMass]
  unfold retainedMass
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases hP : P.card = 0
  · simp [hP]
  · have hP0 : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP
    field_simp

/-- Deleting a small fraction of the ambient graph perturbs ambient class
masses by at most that fraction. -/
lemma retainedMass_error {n m k : ℕ} (hn : 0 < n) (hmn : m ≤ n)
    (τ : Fin m → Fin k) (P : Finset (Fin m)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hP : (univ \ P).card ≤ ρ*(m : ℝ)) (i : Fin k) :
    |retainedMass n τ P i - ((classVertices τ i).card : ℝ)/(n : ℝ)| ≤ ρ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ((classVertices τ i ∩ P).card : ℝ) ≤ (classVertices τ i).card :=
    by exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hd : ((classVertices τ i).card : ℝ) ≤
      (classVertices τ i ∩ P).card + (univ \ P).card := by
    rw [retained_class_eq_deleted]
    exact_mod_cast Finset.card_le_card_sdiff_add_card (s := classVertices τ i) (t := univ \ P)
  have hz : ((univ \ P).card : ℝ) ≤ ρ*n := hP.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) hρ)
  unfold retainedMass
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (div_le_div_of_nonneg_right hs hnR.le))]
  rw [← sub_div]
  apply (div_le_iff₀ hnR).mpr
  linarith

/-- The existing deletion estimate, expressed on the canonical induced core. -/
theorem retained_partition_bounds {m k : ℕ} (G : SimpleGraph (Fin m))
    (τ : Fin m → Fin k) (P : Finset (Fin m)) {a ρ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hρ : 0 ≤ ρ) (hρa : ρ < a/2)
    (hm : 4 ≤ a*m) (hP : ((univ \ P).card : ℝ) ≤ ρ*m)
    (hsize : ∀ i, a*m ≤ (classVertices τ i).card) :
    (∀ i, a/2 ≤ classMass (retainedClasses τ P) i) ∧
    (∀ i j, |blockDensity (inducedGraph G P) (retainedClasses τ P) i j -
      blockDensity G τ i j| ≤ 8*ρ/a) := by
  have hb := vertex_deletion_bounds G τ (univ \ P) ha ha1 hρ hρa hm hP hsize
  have hmR : (0 : ℝ) < m := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hPpos : (0 : ℝ) < P.card := by
    have hcomp : ((univ \ P).card : ℝ) = (m : ℝ)-P.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by simpa using P.card_le_univ)]
    have h := hb.1
    have h' : ((univ \ P).card : ℝ) < m := by exact_mod_cast h
    linarith
  refine ⟨?_, ?_⟩
  · intro i
    rw [retainedClassMass]
    apply (le_div_iff₀ hPpos).mpr
    have hpM : (P.card : ℝ) ≤ m := by exact_mod_cast (by simpa using P.card_le_univ : P.card ≤ m)
    have hh := hb.2.1 i
    rw [← retained_class_eq_deleted] at hh
    nlinarith
  · intro i j
    rw [retainedBlockDensity]
    exact hb.2.2.2 i j

end ComponentTransfer.Lifting
