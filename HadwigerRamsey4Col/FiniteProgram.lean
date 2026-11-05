import HadwigerRamsey4Col.ProgramPatterns
import HadwigerRamsey4Col.Lemma6
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

noncomputable def regionMass {α : Type} [Fintype α] (mass : α → ℝ) (A : Finset α) : ℝ :=
  ∑ i ∈ A, mass i
noncomputable def regionCost {α : Type} [Fintype α] (mass : α → ℝ)
    (p : α → α → ℝ) (A B : Finset α) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ B, mass i*mass j*cost (p i j)
noncomputable def regionDensity {α : Type} [Fintype α] (mass : α → ℝ)
    (p : α → α → ℝ) (A B : Finset α) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ B, mass i*mass j*p i j

/-- A finite component instance with arbitrary finite atom and label types,
and a common bound on the squared component energies. -/
structure FiniteProgram (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] where
  mass : α → ℝ
  mass_pos : ∀ i, 0 < mass i
  mass_sum : ∑ i, mass i = 1
  label : Fin 4 → α → β
  density : Fin 4 → α → α → ℝ
  density_nonneg : ∀ c i j, 0 ≤ density c i j
  density_lt_one : ∀ c i j, density c i j < 1
  density_symm : ∀ c i j, density c i j = density c j i
  density_sum : ∀ i j, ∑ c, density c i j = 1
  density_zero : ∀ c i j, label c i ≠ label c j → density c i j = 0
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  entropy_le : ∀ c b, regionCost mass (density c)
    (univ.filter (fun i => label c i = b)) (univ.filter (fun i => label c i = b)) ≤ bound

namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def part (P : FiniteProgram α β) (c : Fin 4) (b : β) : Finset α :=
  univ.filter (fun i => P.label c i = b)
noncomputable def partMass (P : FiniteProgram α β) (c : Fin 4) (b : β) : ℝ :=
  regionMass P.mass (P.part c b)
noncomputable def partDensity (P : FiniteProgram α β) (c : Fin 4) (b : β) : ℝ :=
  regionDensity P.mass (P.density c) (P.part c b) (P.part c b)
noncomputable def word (P : FiniteProgram α β) (i : α) : Word β := fun c => P.label c i

lemma mass_nonneg (P : FiniteProgram α β) (i : α) : 0 ≤ P.mass i := (P.mass_pos i).le
lemma regionMass_nonneg (P : FiniteProgram α β) (A : Finset α) : 0 ≤ regionMass P.mass A :=
  sum_nonneg (fun i _ => P.mass_nonneg i)
lemma regionCost_nonneg (P : FiniteProgram α β) (c : Fin 4) (A B : Finset α) :
    0 ≤ regionCost P.mass (P.density c) A B := by
  exact sum_nonneg (fun i _ => sum_nonneg (fun j _ => mul_nonneg
    (mul_nonneg (P.mass_nonneg i) (P.mass_nonneg j))
    (cost_nonneg (P.density_nonneg c i j) (P.density_lt_one c i j))))

lemma word_close (P : FiniteProgram α β) (i j : α) : Near (P.word i) (P.word j) := by
  by_contra hn
  have hs := P.density_sum i j
  simp [Fin.sum_univ_succ] at hs
  have h0 := P.density_lt_one 0 i j
  have h1 := P.density_lt_one 1 i j
  have h2 := P.density_lt_one 2 i j
  have h3 := P.density_lt_one 3 i j
  have z0 := P.density_zero 0 i j
  have z1 := P.density_zero 1 i j
  have z2 := P.density_zero 2 i j
  have z3 := P.density_zero 3 i j
  unfold Near word at hn
  grind

lemma patterns (P : FiniteProgram α β) [Nonempty β] : PatternFamily (Set.range P.word) := by
  apply lemma2
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
  exact (near_iff_hamming _ _).mp (P.word_close i j)

lemma partMass_sum (P : FiniteProgram α β) (c : Fin 4) : ∑ b, P.partMass c b = 1 := by
  dsimp [partMass, regionMass, part]
  simp_rw [sum_filter]
  rw [sum_comm]
  simpa using P.mass_sum

lemma part_density_sum (P : FiniteProgram α β) (c : Fin 4) :
    (∑ b, P.partDensity c b) = ∑ i, ∑ j, P.mass i*P.mass j*P.density c i j := by
  simp only [partDensity, regionDensity, part, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp only [sum_ite_eq, mem_univ, if_true]
  apply sum_congr rfl
  intro j hj
  split_ifs with h
  · rfl
  · rw [P.density_zero c i j (Ne.symm h), mul_zero]

lemma all_density_sum (P : FiniteProgram α β) : ∑ c, ∑ b, P.partDensity c b = 1 := by
  simp_rw [P.part_density_sum]
  rw [sum_comm]
  trans ∑ i, ∑ j, P.mass i*P.mass j
  · apply sum_congr rfl
    intro i hi
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [← mul_sum, P.density_sum, mul_one]
  · rw [← sum_mul_sum, P.mass_sum, one_mul]

end FiniteProgram

noncomputable def instanceProgram (I : ComponentInstance) : FiniteProgram (Fin I.k) (Fin I.k) where
  mass := I.mass
  mass_pos := I.mass_pos
  mass_sum := I.mass_sum
  label := I.label
  density := I.density
  density_nonneg := I.density_nonneg
  density_lt_one := I.density_lt_one
  density_symm := I.density_symm
  density_sum := I.density_sum
  density_zero := I.density_zero
  bound := I.objective^2
  bound_nonneg := sq_nonneg _
  entropy_le := by
    intro c b
    have he := I.energy_le_objective c b
    have hn := I.partEntropy_nonneg c b
    have hs := sq_sqrt hn
    change sqrt (I.partEntropy c b) ≤ I.objective at he
    have hh := sqrt_nonneg (I.partEntropy c b)
    change I.partEntropy c b ≤ I.objective^2
    nlinarith

end HadwigerRamsey4Col
