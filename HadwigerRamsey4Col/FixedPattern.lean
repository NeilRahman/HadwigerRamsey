import HadwigerRamsey4Col.ComponentCapacity

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col
namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma colour_linear_capacity (P : FiniteProgram α β) (ht : P.bound ≤ threshold) (c : Fin 4) :
    (∑ b, P.partDensity c b) ≤ (16/25 : ℝ)*sqrt threshold := by
  have hh := sum_le_sum (fun b (_ : b ∈ univ) => P.part_linear_capacity ht c b)
  simpa [← mul_sum, P.partMass_sum] using hh

lemma fixed_colour_capacity (P : FiniteProgram α β) (ht : P.bound ≤ threshold)
    (c : Fin 4) (b : β) (hfix : ∀ i, P.label c i=b) :
    (∑ b, P.partDensity c b) ≤ capacityF threshold 1 := by
  have hpart : P.part c b = univ := by ext i; simp [part,hfix]
  have he := P.entropy_le c b
  change regionCost P.mass (P.density c) (P.part c b) (P.part c b) ≤ P.bound at he
  rw [hpart] at he
  have hh := P.region_capacity c univ (he.trans ht)
  have hm : regionMass P.mass univ=1 := P.mass_sum
  rw [hm] at hh
  simpa [P.part_density_sum,regionDensity] using hh

/-- Two fixed component coordinates are impossible below the rational threshold. -/
theorem no_two_fixed (P : FiniteProgram α β) (ht : P.bound ≤ threshold)
    (c d : Fin 4) (hcd : c ≠ d) (b e : β)
    (hc : ∀ i, P.label c i=b) (hd : ∀ i, P.label d i=e) : False := by
  have h0 := P.colour_linear_capacity ht 0
  have h1 := P.colour_linear_capacity ht 1
  have h2 := P.colour_linear_capacity ht 2
  have h3 := P.colour_linear_capacity ht 3
  have hC := P.fixed_colour_capacity ht c b hc
  have hD := P.fixed_colour_capacity ht d e hd
  have hs := P.all_density_sum
  simp [Fin.sum_univ_succ] at hs
  have hbad := fixed_capacity_sum_lt
  fin_cases c <;> fin_cases d <;> norm_num at hcd <;> linarith!

end FiniteProgram
end HadwigerRamsey4Col
