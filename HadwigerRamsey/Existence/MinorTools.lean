import HadwigerRamsey.Graph

open Set
namespace HadwigerRamsey

/-- Injective graph homomorphisms preserve branch-set clique minors. -/
theorem HasCliqueMinor.map_injective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {s : ℕ} (h : HasCliqueMinor G s) (f : G →g H) (hf : Function.Injective f) :
    HasCliqueMinor H s := by
  classical
  obtain ⟨B,hc,hd,he⟩ := h
  refine ⟨fun i => f '' B i,?_,?_,?_⟩
  · intro i
    let g : (G.induce (B i)) →g (H.induce (f '' B i)) :=
      { toFun := fun x => ⟨f x,⟨x,x.property,rfl⟩⟩
        map_rel' := fun h => f.map_adj h }
    apply (hc i).map g
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro w ⟨u,hu,rfl⟩ ⟨v,hv,hvu⟩
    exact Set.disjoint_left.mp (hd i j hij) hu (hf hvu ▸ hv)
  · intro i j hij
    obtain ⟨u,hu,v,hv,huv⟩ := he i j hij
    exact ⟨f u,⟨u,hu,rfl⟩,f v,⟨v,hv,rfl⟩,f.map_adj huv⟩

/-- A minor supported in the image of an injection pulls back to its comap. -/
theorem HasCliqueMinor.comap_of_range {V W : Type*} {G : SimpleGraph W} {s : ℕ}
    (f : V → W) (hf : Function.Injective f) (B : Fin s → Set W)
    (hc : ∀ i, (G.induce (B i)).Connected)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (he : ∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)
    (hr : ∀ i, B i ⊆ range f) : HasCliqueMinor (G.comap f) s := by
  classical
  have hex : ∀ i (x : B i), ∃ u, f u = x := fun i x => hr i x.property
  let r := fun i (x : B i) => (hex i x).choose
  have hfr : ∀ i (x : B i), f (r i x) = x := fun i x => (hex i x).choose_spec
  refine ⟨fun i => f ⁻¹' B i,?_,?_,?_⟩
  · intro i
    let g : (G.induce (B i)) →g ((G.comap f).induce (f ⁻¹' B i)) :=
      { toFun := fun x => ⟨r i x,by change f (r i x) ∈ B i; rw [hfr]; exact x.property⟩
        map_rel' := by intro x y h; change G.Adj (x : W) (y : W) at h; change G.Adj (f (r i x)) (f (r i y)); simpa only [hfr] using h }
    apply (hc i).map g
    intro x
    refine ⟨⟨f x,x.property⟩,?_⟩
    apply Subtype.ext
    exact hf (hfr i ⟨f x,x.property⟩)
  · intro i j hij
    exact (hd i j hij).preimage f
  · intro i j hij
    obtain ⟨u,hu,v,hv,huv⟩ := he i j hij
    refine ⟨r i ⟨u,hu⟩,?_,r j ⟨v,hv⟩,?_,?_⟩
    · change f (r i ⟨u,hu⟩) ∈ B i; simpa only [hfr] using hu
    · change f (r j ⟨v,hv⟩) ∈ B j; simpa only [hfr] using hv
    · change G.Adj (f (r i ⟨u,hu⟩)) (f (r j ⟨v,hv⟩)); simpa only [hfr] using huv

theorem hadwigerNumber_comap_le {n m : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin m → Fin n) (hf : Function.Injective f) :
    hadwigerNumber (G.comap f) ≤ hadwigerNumber G := by
  apply cliqueMinor_le_hadwigerNumber
  exact (hadwigerNumber_hasCliqueMinor (G.comap f)).map_injective
    ⟨f,fun h => h⟩ hf

end HadwigerRamsey

namespace HadwigerRamsey
open Set
lemma reachable_same_label {V I : Type*} {G : SimpleGraph V} (c : V → I)
    (h : ∀ u v, G.Adj u v → c u = c v) {u v : V} (hp : G.Reachable u v) : c u = c v := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => rfl
  | cons huv p ih => exact (h _ _ huv).trans ih

theorem HasCliqueMinor.in_one_fiber {V I : Type*} {G : SimpleGraph V} {s : ℕ}
    (hs : 0 < s) (c : V → I) (h : ∀ u v, G.Adj u v → c u = c v)
    (hm : HasCliqueMinor G s) :
    ∃ t : I, ∃ B : Fin s → Set V,
      (∀ i, (G.induce (B i)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v) ∧
      ∀ i v, v ∈ B i → c v = t := by
  classical
  obtain ⟨B,hc,hd,he⟩ := hm
  let z : Fin s := ⟨0,hs⟩
  let x := fun i => (hc i).nonempty.some
  have hconst : ∀ i (v : B i), c v = c (x i) := by
    intro i v
    exact reachable_same_label (fun v : B i => c v)
      (fun u v huv => h _ _ huv) ((hc i).preconnected v (x i))
  refine ⟨c (x z),B,hc,hd,he,?_⟩
  intro i v hv
  have hi : c (x i) = c (x z) := by
    by_cases hiz : i = z
    · exact congrArg (fun i => c (x i)) hiz
    · obtain ⟨u,hu,w,hw,huw⟩ := he i z hiz
      exact (hconst i ⟨u,hu⟩).symm.trans ((h _ _ huw).trans (hconst z ⟨w,hw⟩))
  exact (hconst i ⟨v,hv⟩).trans hi

 theorem hadwigerNumber_le_of_fibers {n m : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (f : Fin 2 → Fin m → Fin n) (hf : ∀ i, Function.Injective (f i))
    (hcover : ∀ i v, c v = i → v ∈ range (f i))
    (hedge : ∀ u v, G.Adj u v → c u = c v) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i, (hadwigerNumber (G.comap (f i)) : ℝ) ≤ R) : (hadwigerNumber G : ℝ) ≤ R := by
  by_cases hs : 0 < hadwigerNumber G
  · obtain ⟨t,B,hc,hd,he,hfiber⟩ := (hadwigerNumber_hasCliqueMinor G).in_one_fiber hs c hedge
    have hm := HasCliqueMinor.comap_of_range (f t) (hf t) B hc hd he
      (fun i v hv => hcover t v (hfiber i v hv))
    have hh : hadwigerNumber G ≤ hadwigerNumber (G.comap (f t)) := cliqueMinor_le_hadwigerNumber hm
    exact (show (hadwigerNumber G : ℝ) ≤ hadwigerNumber (G.comap (f t)) by exact_mod_cast hh).trans (hb t)
  · have hh : hadwigerNumber G = 0 := by omega
    simpa only [hh,Nat.cast_zero] using hR
end HadwigerRamsey
