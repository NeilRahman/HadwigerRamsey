import HadwigerRamsey4Col.BlockAverages

open Real Finset
open scoped BigOperators Classical
namespace HadwigerRamsey4Col
namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

abbrev Profile (P : FiniteProgram α β) := {w : Word β // w ∈ Set.range P.word}

noncomputable instance profileFintype (P : FiniteProgram α β) : Fintype P.Profile :=
  Fintype.ofFinite _

noncomputable def profileMap (P : FiniteProgram α β) (i : α) : P.Profile :=
  ⟨P.word i, ⟨i,rfl⟩⟩
noncomputable def profileFiber (P : FiniteProgram α β) (w : P.Profile) : Finset α :=
  univ.filter (fun i => P.profileMap i=w)

lemma profileFiber_nonempty (P : FiniteProgram α β) (w : P.Profile) :
    (P.profileFiber w).Nonempty := by
  obtain ⟨i,hi⟩ := w.property
  refine ⟨i,?_⟩
  simp only [profileFiber, mem_filter, mem_univ, true_and]
  exact Subtype.ext hi

lemma sum_profile_fibers (P : FiniteProgram α β) (f : α → ℝ) :
    (∑ w : P.Profile, ∑ i ∈ P.profileFiber w, f i) = ∑ i, f i := by
  exact sum_fiberwise univ P.profileMap f

noncomputable def mergedMass (P : FiniteProgram α β) (w : P.Profile) : ℝ :=
  regionMass P.mass (P.profileFiber w)
noncomputable def mergedDensity (P : FiniteProgram α β) (c : Fin 4) (w v : P.Profile) : ℝ :=
  blockAverage P.mass (P.density c) (P.profileFiber w) (P.profileFiber v)

lemma mergedMass_pos (P : FiniteProgram α β) (w : P.Profile) : 0 < P.mergedMass w :=
  sum_pos (fun i _ => P.mass_pos i) (P.profileFiber_nonempty w)
lemma mergedMass_sum (P : FiniteProgram α β) : ∑ w, P.mergedMass w = 1 := by
  rw [show (∑ w, P.mergedMass w) = ∑ i, P.mass i from P.sum_profile_fibers P.mass]
  exact P.mass_sum

lemma profileFiber_label (P : FiniteProgram α β) (w : P.Profile) (i : α)
    (hi : i ∈ P.profileFiber w) (c : Fin 4) : P.label c i = w.val c := by
  have h := (mem_filter.mp hi).2
  exact congrFun (congrArg Subtype.val h) c

lemma mergedDensity_sum (P : FiniteProgram α β) (w v : P.Profile) :
    ∑ c, P.mergedDensity c w v = 1 := by
  have hden : P.mergedMass w*P.mergedMass v ≠ 0 :=
    mul_ne_zero (ne_of_gt (P.mergedMass_pos w)) (ne_of_gt (P.mergedMass_pos v))
  dsimp [mergedDensity, blockAverage]
  rw [← sum_div]
  apply (div_eq_one_iff_eq _).mpr
  · dsimp [regionDensity]
    rw [sum_comm]
    trans ∑ i ∈ P.profileFiber w, ∑ j ∈ P.profileFiber v, P.mass i*P.mass j
    · apply sum_congr rfl
      intro i hi
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← mul_sum, P.density_sum, mul_one]
    · exact (region_mass_product P.mass _ _).symm
  · exact hden

lemma mergedDensity_zero (P : FiniteProgram α β) (c : Fin 4) (w v : P.Profile)
    (h : w.val c ≠ v.val c) : P.mergedDensity c w v = 0 := by
  dsimp [mergedDensity, blockAverage, regionDensity]
  have he : (∑ i ∈ P.profileFiber w, ∑ j ∈ P.profileFiber v,
      P.mass i*P.mass j*P.density c i j) = 0 := by
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro j hj
    rw [P.density_zero c i j (by
      rw [P.profileFiber_label w i hi c, P.profileFiber_label v j hj c]
      exact h), mul_zero]
  rw [he, zero_div]

end FiniteProgram
end HadwigerRamsey4Col
