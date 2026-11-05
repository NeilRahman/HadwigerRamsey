import HadwigerRamsey4Col.Program
import HadwigerRamsey4Col.Parameters

open Real Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace HadwigerRamsey4Col

/-- The three pairings and the spanning partition, on four atoms. -/
def optimalLabel : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,0,1,1], ![0,1,0,1], ![0,1,1,0], ![0,0,0,0]]

noncomputable def optimalDensity (c i j : Fin 4) : ℝ :=
  if i=j then (if c=3 then 0 else 1/3)
  else if c=3 then 1-parameter else if optimalLabel c i=optimalLabel c j then parameter else 0

noncomputable def attainingInstance : ComponentInstance where
  k := 4
  k_pos := by norm_num
  mass := fun _ => 1/4
  mass_pos := by intro i; norm_num
  mass_sum := by norm_num
  label := optimalLabel
  density := optimalDensity
  density_nonneg := by
    intro c i j
    obtain ⟨hp0,hp1,_⟩ := parameter_spec
    fin_cases c <;> fin_cases i <;> fin_cases j <;>
      norm_num [optimalDensity, optimalLabel, Fin.ext_iff] <;> linarith
  density_lt_one := by
    intro c i j
    obtain ⟨hp0,hp1,_⟩ := parameter_spec
    fin_cases c <;> fin_cases i <;> fin_cases j <;>
      norm_num [optimalDensity, optimalLabel, Fin.ext_iff] <;> linarith
  density_symm := by
    intro c i j
    simp only [optimalDensity, eq_comm]
  density_sum := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ, optimalDensity, optimalLabel, Fin.ext_iff]
  density_zero := by
    intro c i j hij
    by_cases he : i=j
    · subst j
      exact (hij rfl).elim
    by_cases hc : c=3
    · subst c
      fin_cases i <;> fin_cases j <;> simp [optimalLabel] at hij
    simp [optimalDensity, he, hc, hij]

lemma parameter_log_relation :
    log (1-parameter) = log (3/2 : ℝ)+6*log parameter := by
  have hp := parameter_spec
  have he : 1-parameter = (3/2 : ℝ)*parameter^6 := by nlinarith [hp.2.2]
  rw [he, log_mul (by norm_num) (pow_ne_zero 6 (ne_of_gt hp.1)), log_pow]
  norm_num

lemma tStar_pos : 0 < tStar parameter := by
  have hl := log_neg parameter_spec.1 parameter_spec.2.1
  dsimp [tStar]
  linarith

set_option maxRecDepth 4096 in
lemma attaining_entropy (c b : Fin 4) :
    attainingInstance.partEntropy c b =
      if c=3 then (if b=0 then tStar parameter else 0)
      else if b=0 ∨ b=1 then tStar parameter else 0 := by
  have hl := parameter_log_relation
  have hb : log (2/3 : ℝ) = -log (3/2 : ℝ) := by
    rw [← log_inv]
    norm_num
  change (∑ i : Fin 4 with optimalLabel c i=b, ∑ j : Fin 4 with optimalLabel c j=b,
    (1/4 : ℝ)*(1/4 : ℝ)*(-log (1-optimalDensity c i j))) = _
  simp only [sum_filter]
  fin_cases c <;> fin_cases b <;>
    simp only [Fin.sum_univ_four] <;>
    norm_num [optimalLabel, optimalDensity]
    <;> dsimp [tStar] <;> norm_num [hb] <;> linarith

lemma attaining_objective : attainingInstance.objective = sqrt (tStar parameter) := by
  let : NeZero attainingInstance.k := ⟨by change (4:ℕ) ≠ 0; norm_num⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨⟨c,b⟩,rfl⟩
    apply sqrt_le_sqrt
    change Fin 4 at b
    change attainingInstance.partEntropy c b ≤ tStar parameter
    rw [attaining_entropy]
    split_ifs <;> linarith [tStar_pos]
  · have h := attainingInstance.energy_le_objective 3 0
    change sqrt (attainingInstance.partEntropy 3 (0 : Fin 4)) ≤ _ at h
    simpa [attaining_entropy] using h

lemma beta4_upper : beta4 ≤ sqrt (tStar parameter) :=
  (ComponentTransfer.beta_le_objective (by norm_num : 2 ≤ 4) attainingInstance).trans
    attaining_objective.le

end HadwigerRamsey4Col
