import HadwigerRamsey.Main.Final

open scoped Classical
open Real
namespace HadwigerRamsey

/-- Theorem 1.3: every sufficiently large three-colour complete graph has
a colour with the manuscript's Hadwiger lower bound. -/
theorem mainthm (ε : ℝ) (hε : 0<ε) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ G : Fin 3→SimpleGraph (Fin n), IsThreeDecomposition G →
      ∃ i : Fin 3, (1-ε)*beta*n/sqrt (log (n:ℝ))≤(hadwigerNumber (G i):ℝ) := by
  by_cases hε1 : ε≤1
  · exact Main.mainthm_small ε hε hε1
  · refine ⟨2,?_⟩
    intro n hn G hG
    refine ⟨0,?_⟩
    have hb:=beta_pos
    apply le_trans (b:=0) ?_ (by positivity)
    apply div_nonpos_of_nonpos_of_nonneg
    · have hh : 1-ε≤0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hh hb.le) (Nat.cast_nonneg n)
    · exact sqrt_nonneg _

end HadwigerRamsey
