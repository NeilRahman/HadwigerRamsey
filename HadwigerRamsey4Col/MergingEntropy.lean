import HadwigerRamsey4Col.Merging

open Real Finset
open scoped BigOperators Classical
namespace HadwigerRamsey4Col
namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma sum_profile_part (P : FiniteProgram α β) (c : Fin 4) (b : β) (f : α → ℝ) :
    (∑ w : P.Profile with w.val c=b, ∑ i ∈ P.profileFiber w, f i) =
      ∑ i ∈ P.part c b, f i := by
  have hh := sum_fiberwise_of_maps_to
    (s := P.part c b) (t := univ.filter (fun w : P.Profile => w.val c=b))
    (g := P.profileMap) (fun i (hi : i ∈ P.part c b) => by
      simpa [part, profileMap, word] using hi) f
  have he : ∀ w : P.Profile, w.val c=b →
      ((P.part c b).filter (fun i => P.profileMap i=w)) = P.profileFiber w := by
    intro w hw
    ext i
    simp only [part, profileFiber, mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hi
      refine ⟨?_,hi⟩
      have hval := congrFun (congrArg Subtype.val hi) c
      exact hval.trans hw
  calc
    _ = ∑ w ∈ univ.filter (fun w : P.Profile => w.val c=b),
      ∑ i ∈ (P.part c b).filter (fun i => P.profileMap i=w), f i := by
        apply sum_congr rfl
        intro w hw
        rw [he w (mem_filter.mp hw).2]
    _ = _ := hh

lemma sum_profile_cost (P : FiniteProgram α β) (c : Fin 4) (b : β) :
    (∑ w : P.Profile with w.val c=b, ∑ v : P.Profile with v.val c=b,
      regionCost P.mass (P.density c) (P.profileFiber w) (P.profileFiber v)) =
      regionCost P.mass (P.density c) (P.part c b) (P.part c b) := by
  unfold regionCost
  calc
    _ = ∑ w : P.Profile with w.val c=b, ∑ i ∈ P.profileFiber w,
        ∑ v : P.Profile with v.val c=b, ∑ j ∈ P.profileFiber v,
          P.mass i*P.mass j*cost (P.density c i j) := by
      apply sum_congr rfl
      intro w hw
      rw [sum_comm]
    _ = _ := by
      simp_rw [P.sum_profile_part c b]

lemma merged_entropy_le (P : FiniteProgram α β) (c : Fin 4) (b : β) :
    regionCost P.mergedMass (P.mergedDensity c)
      (univ.filter (fun w : P.Profile => w.val c=b))
      (univ.filter (fun w : P.Profile => w.val c=b)) ≤ P.bound := by
  apply le_trans _ (P.entropy_le c b)
  change _ ≤ regionCost P.mass (P.density c) (P.part c b) (P.part c b)
  rw [← P.sum_profile_cost c b]
  apply sum_le_sum
  intro w hw
  apply sum_le_sum
  intro v hv
  exact blockAverage_cost P.mass (P.density c) _ _ P.mass_pos
    (P.profileFiber_nonempty w) (P.profileFiber_nonempty v) (P.density_lt_one c)

/-- Merging equal full label words preserves feasibility and the entropy bound. -/
noncomputable def merge (P : FiniteProgram α β) : FiniteProgram P.Profile β where
  mass := P.mergedMass
  mass_pos := P.mergedMass_pos
  mass_sum := P.mergedMass_sum
  label := fun c w => w.val c
  density := P.mergedDensity
  density_nonneg := fun c w v => (blockAverage_bounds P.mass (P.density c) _ _ P.mass_pos
    (P.profileFiber_nonempty w) (P.profileFiber_nonempty v)
    (P.density_nonneg c) (P.density_lt_one c)).1
  density_lt_one := fun c w v => (blockAverage_bounds P.mass (P.density c) _ _ P.mass_pos
    (P.profileFiber_nonempty w) (P.profileFiber_nonempty v)
    (P.density_nonneg c) (P.density_lt_one c)).2
  density_symm := fun c _w _v => blockAverage_symm P.mass (P.density c) (P.density_symm c) _ _
  density_sum := P.mergedDensity_sum
  density_zero := P.mergedDensity_zero
  bound := P.bound
  bound_nonneg := P.bound_nonneg
  entropy_le := P.merged_entropy_le

lemma merge_word_injective (P : FiniteProgram α β) : Function.Injective P.merge.word := by
  intro w v h
  exact Subtype.ext h

end FiniteProgram
end HadwigerRamsey4Col
