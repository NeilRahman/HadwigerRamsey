import HadwigerRamsey4Col.Capacity

open Real
namespace HadwigerRamsey4Col

/-- Lemma 6 of `four_colour_analytic.tex`, including zero component mass. -/
theorem lemma6 (t s : ℝ) (ht : 0 < t) (hs : 0 ≤ s) :
    capacityF t s ≤ (16/25 : ℝ)*sqrt t*s ∧
    capacityG t s ≤ (413/500 : ℝ)*sqrt t*s :=
  ⟨capacityF_bound ht hs, capacityG_bound ht hs⟩

end HadwigerRamsey4Col
