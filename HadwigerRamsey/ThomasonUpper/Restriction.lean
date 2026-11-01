import HadwigerRamsey.ThomasonUpper.DensityDeletion

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

attribute [-instance] SimpleGraph.instDecidableComapAdj in
theorem card_comap_interedges {A B : Type*} [DecidableEq A] [DecidableEq B]
    (G : SimpleGraph B) (f : A → B) (hf : Function.Injective f) (S T : Finset A) :
    ((G.comap f).interedges S T).card = (G.interedges (S.image f) (T.image f)).card := by
  classical
  apply card_bij (fun e _ => (f e.1,f e.2))
  · intro e he
    obtain ⟨hx,hy,hxy⟩ := (G.comap f).mem_interedges_iff.mp he
    exact G.mem_interedges_iff.mpr ⟨mem_image_of_mem f hx,mem_image_of_mem f hy,hxy⟩
  · intro e he e' he' h
    exact Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  · rintro ⟨v,w⟩ he
    obtain ⟨hx,hy,hxy⟩ := G.mem_interedges_iff.mp he
    obtain ⟨x,hxS,rfl⟩ := mem_image.mp hx
    obtain ⟨y,hyT,rfl⟩ := mem_image.mp hy
    exact ⟨(x,y),(G.comap f).mem_interedges_iff.mpr ⟨hxS,hyT,hxy⟩,rfl⟩

attribute [-instance] SimpleGraph.instDecidableComapAdj in
theorem edgeDensity_comap {A B : Type*} [DecidableEq A] [DecidableEq B]
    (G : SimpleGraph B) (f : A → B) (hf : Function.Injective f) (S T : Finset A) :
    (G.comap f).edgeDensity S T = G.edgeDensity (S.image f) (T.image f) := by
  classical
  simp only [SimpleGraph.edgeDensity_def,card_comap_interedges G f hf,
    card_image_of_injective _ hf]

attribute [-instance] SimpleGraph.instDecidableComapAdj in
theorem internalDensity_comap {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (G : SimpleGraph B) (f : A → B)
    (hf : Function.Injective f) (S : Finset A) :
    internalDensity (G.comap f) S = internalDensity G (S.image f) := by
  classical
  have hh := card_comap_interedges G f hf S S
  have hl := card_internal_interedges (G.comap f) S
  have hr := card_internal_interedges G (S.image f)
  have hc := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (hl.symm.trans (hh.trans hr))
  simp only [internalDensity,card_image_of_injective _ hf]
  exact congrArg (fun c : ℕ => (c : ℝ)/(S.card.choose 2 : ℝ)) hc

noncomputable def survivorEquiv {n : ℕ} (Z : Finset (Fin n)) :
    Fin (n-Z.card) ≃ {v : Fin n // v ∉ Z} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,Fintype.card_of_subtype (univ \ Z) (by intro v; simp),
      card_sdiff_of_subset (subset_univ Z),card_univ,Fintype.card_fin])

noncomputable def survivorMap {n : ℕ} (Z : Finset (Fin n))
    (v : Fin (n-Z.card)) : Fin n := (survivorEquiv Z v).val

theorem survivorMap_injective {n : ℕ} (Z : Finset (Fin n)) : Function.Injective (survivorMap Z) :=
  Subtype.val_injective.comp (survivorEquiv Z).injective

theorem survivorMap_not_mem {n : ℕ} (Z : Finset (Fin n)) (v : Fin (n-Z.card)) :
    survivorMap Z v ∉ Z := (survivorEquiv Z v).property

noncomputable def restrictedGraph {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) :
    SimpleGraph (Fin (n-Z.card)) := G.comap (survivorMap Z)

noncomputable def restrictedClasses {n k : ℕ} (classes : Fin n → Fin k) (Z : Finset (Fin n)) :
    Fin (n-Z.card) → Fin k := fun v => classes (survivorMap Z v)

theorem image_restricted_class {n k : ℕ} (classes : Fin n → Fin k) (Z : Finset (Fin n)) (i : Fin k) :
    (classVertices (restrictedClasses classes Z) i).image (survivorMap Z) = classVertices classes i \ Z := by
  ext v
  simp only [mem_image,classVertices,mem_filter,mem_univ,true_and,restrictedClasses,mem_sdiff]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(mem_filter.mp hu).2,survivorMap_not_mem Z u⟩
  · rintro ⟨hi,hv⟩
    obtain ⟨u,hu⟩ := (survivorEquiv Z).surjective ⟨v,hv⟩
    have he : survivorMap Z u = v := congrArg Subtype.val hu
    exact ⟨u,mem_filter.mpr ⟨mem_univ _,by simpa only [he] using hi⟩,he⟩

theorem restrictedClassMass {n k : ℕ} (classes : Fin n → Fin k) (Z : Finset (Fin n)) (i : Fin k) :
    classMass (restrictedClasses classes Z) i = deletedClassMass classes Z i := by
  have hc := congrArg Finset.card (image_restricted_class classes Z i)
  rw [card_image_of_injective _ (survivorMap_injective Z)] at hc
  change ((classVertices (restrictedClasses classes Z) i).card : ℝ)/((n-Z.card : ℕ) : ℝ) = _
  simp only [deletedClassMass,hc]

attribute [-instance] SimpleGraph.instDecidableComapAdj in
theorem restrictedBlockDensity {n k : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (Z : Finset (Fin n)) (i j : Fin k) :
    blockDensity (restrictedGraph G Z) (restrictedClasses classes Z) i j = deletedBlockDensity G classes Z i j := by
  unfold blockDensity deletedBlockDensity
  split
  · exact (internalDensity_comap G _ (survivorMap_injective Z) _).trans
      (congrArg (internalDensity G) (image_restricted_class classes Z i))
  · exact congrArg (fun q : ℚ => (q : ℝ))
      ((edgeDensity_comap G _ (survivorMap_injective Z) _ _).trans
        (congrArg₂ G.edgeDensity (image_restricted_class classes Z i) (image_restricted_class classes Z j)))

end HadwigerRamsey.ThomasonUpper
