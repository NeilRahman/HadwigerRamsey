import ComponentTransfer.ConstructionParameters
import ComponentTransfer.ConstructionFinite
import ComponentTransfer.ConstructionAsymptotic
import ComponentTransfer.ConstructionRounding

open scoped Topology BigOperators Classical
open Filter Real HadwigerRamsey

namespace ComponentTransfer

/-- The random construction for the component optimization constant. -/
theorem constructionBound (r : ℕ) (hr : 2 ≤ r) : ConstructionBound r (beta r) := by
  intro ε hε
  obtain ⟨I, hI⟩ := exists_objective_lt hr hε
  obtain ⟨d, hd, hprob, hdensity, henergy, hmargin⟩ :=
    Construction.exists_construction_parameter hr I hI
  obtain ⟨τ, hτ⟩ := Construction.exists_convergent_partitions I.k_pos I.mass
    (fun i => (I.mass_pos i).le) I.mass_sum
  obtain ⟨N, hN⟩ := Construction.finite_construction I hd hprob hdensity
  have hB : 0 < beta r + ε := by have := beta_pos hr; linarith
  have hlarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ (beta r + ε)*n/sqrt (log (n : ℝ)) := by
    have h := Ramsey.order_div_sqrt_log_atTop.const_mul_atTop hB
    simpa only [mul_div_assoc] using h.eventually_ge_atTop 1
  have hcomponents : ∀ᶠ n : ℕ in atTop, ∀ c t, 0 < I.energy c t →
      N ≤ Construction.componentSize (τ n) (I.label c) t ∧
      d < sqrt (blockLambda ((τ n) ∘ Construction.componentMap (τ n) (I.label c) t)
        (I.density c)) ∧
      (1+d)*sqrt (blockLambda ((τ n) ∘ Construction.componentMap (τ n) (I.label c) t)
        (I.density c)) * (Construction.componentSize (τ n) (I.label c) t : ℝ) /
        sqrt (log (Construction.componentSize (τ n) (I.label c) t : ℝ)) ≤
        (beta r+ε)*n/sqrt (log (n : ℝ)) := by
    apply Filter.eventually_all.mpr
    intro c
    apply Filter.eventually_all.mpr
    intro t
    by_cases he : 0 < I.energy c t
    · exact (Construction.eventually_component_bounds I τ hτ c t he hd
        (henergy c t he) hmargin N).mono (fun n hn _ => hn)
    · exact Eventually.of_forall (fun n h => (he h).elim)
  filter_upwards [hlarge, hcomponents] with n hn hc
  exact hN n (τ n)
    (fun c t => Construction.componentSize (τ n) (I.label c) t)
    (fun c t => Construction.componentMap (τ n) (I.label c) t)
    (fun c t => Construction.componentMap_strictMono (τ n) (I.label c) t)
    (fun c t => Construction.componentMap_label (τ n) (I.label c) t)
    (fun c t => Construction.componentMap_cover (τ n) (I.label c) t)
    ((beta r+ε)*n/sqrt (log (n : ℝ))) hn hc

/-- Theorem 4: for every fixed number of colours at least two and every
positive error, all sufficiently large orders have a colouring satisfying
the manuscript's upper bound in every colour. -/
theorem theorem4 (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ G : Fin r → SimpleGraph (Fin n),
      IsDecomposition G ∧ ∀ c : Fin r,
        (hadwigerNumber (G c) : ℝ) ≤ (beta r+ε)*(n : ℝ)/sqrt (log (n : ℝ)) :=
  eventually_atTop.mp (constructionBound r hr ε hε)

end ComponentTransfer
