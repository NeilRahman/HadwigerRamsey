import HadwigerRamsey4Col.MergingEntropy

open Real Finset
open scoped BigOperators Classical
namespace HadwigerRamsey4Col
namespace FiniteProgram
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

noncomputable def recolour (P : FiniteProgram α β) (σ : Equiv.Perm (Fin 4)) : FiniteProgram α β where
  mass := P.mass
  mass_pos := P.mass_pos
  mass_sum := P.mass_sum
  label := fun c => P.label (σ c)
  density := fun c => P.density (σ c)
  density_nonneg := fun c => P.density_nonneg (σ c)
  density_lt_one := fun c => P.density_lt_one (σ c)
  density_symm := fun c => P.density_symm (σ c)
  density_sum := by
    intro i j
    exact (Equiv.sum_comp σ (fun c => P.density c i j)).trans (P.density_sum i j)
  density_zero := fun c => P.density_zero (σ c)
  bound := P.bound
  bound_nonneg := P.bound_nonneg
  entropy_le := fun c => P.entropy_le (σ c)

noncomputable def reindex (P : FiniteProgram α β) (e : γ ≃ α) : FiniteProgram γ β where
  mass := fun i => P.mass (e i)
  mass_pos := fun i => P.mass_pos (e i)
  mass_sum := (e.sum_comp P.mass).trans P.mass_sum
  label := fun c i => P.label c (e i)
  density := fun c i j => P.density c (e i) (e j)
  density_nonneg := fun c i j => P.density_nonneg c (e i) (e j)
  density_lt_one := fun c i j => P.density_lt_one c (e i) (e j)
  density_symm := fun c i j => P.density_symm c (e i) (e j)
  density_sum := fun i j => P.density_sum (e i) (e j)
  density_zero := fun c i j => P.density_zero c (e i) (e j)
  bound := P.bound
  bound_nonneg := P.bound_nonneg
  entropy_le := by
    intro c b
    apply le_trans _ (P.entropy_le c b)
    dsimp [regionCost]
    simp_rw [sum_filter]
    have hi (i : α) :
        (∑ j : γ, if P.label c (e j)=b then P.mass i*P.mass (e j)*cost (P.density c i (e j)) else 0) =
        ∑ j : α, if P.label c j=b then P.mass i*P.mass j*cost (P.density c i j) else 0 :=
      Equiv.sum_comp e (fun j => if P.label c j=b then P.mass i*P.mass j*cost (P.density c i j) else 0)
    simp_rw [hi]
    exact (Equiv.sum_comp e (fun i => if P.label c i=b then
      ∑ j : α, if P.label c j=b then P.mass i*P.mass j*cost (P.density c i j) else 0
      else 0)).le

end FiniteProgram
end HadwigerRamsey4Col
