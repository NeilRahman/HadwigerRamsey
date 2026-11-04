import HadwigerRamsey.Main.OptimizationData

open scoped Classical BigOperators
open Finset Real
namespace HadwigerRamsey.Main

/-- The numerical conclusion supplied by the public approximate optimization theorem. -/
def ApproxBound (ζ ξ : ℝ) : Prop :=
  ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 1/ζ →
    ∀ (α p : Fin k → ℝ) (qB qG : Fin k → Fin k → ℝ),
    (∀ i, 0 ≤ α i) → (∑ i, α i = 1) →
    (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1-ζ) →
    (∀ i j, 0 ≤ qB i j) → (∀ i j, qB i j ≤ 1-ζ) →
    (∀ i j, 0 ≤ qG i j) → (∀ i j, qG i j ≤ 1-ζ) →
    (∀ i j, qB i j = qB j i) → (∀ i j, qG i j = qG j i) →
    ¬ ((∀ i, 1-ξ ≤ p i+qB i i+qG i i) ∧
       (∀ i j, i ≠ j → 1-ξ ≤ qB i j+qG i j) ∧
       (∀ i, α i * sqrt (-log (1-p i)) ≤ beta-ζ) ∧
       sqrt (-(∑ i, ∑ j, α i*α j*log (1-qB i j))) ≤ beta-ζ ∧
       sqrt (-(∑ i, ∑ j, α i*α j*log (1-qG i j))) ≤ beta-ζ)

/-- Fill the last exceptional row and column, then invoke the optimization contradiction. -/
theorem configuration_contradiction {m : ℕ} {ζ ξ : ℝ}
    (hopt : ApproxBound ζ ξ) (hξ : 0 ≤ ξ)
    (hζhalf : ζ ≤ 1/2) (hζbeta : ζ ≤ beta/100)
    (α : Fin (m+1) → ℝ) (p : Fin m → ℝ) (qB qG : Fin m → Fin m → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1)
    (hcount : (m+1 : ℝ) ≤ 1/ζ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1-ζ)
    (hB0 : ∀ i j, 0 ≤ qB i j) (hB1 : ∀ i j, qB i j ≤ 1-ζ)
    (hG0 : ∀ i j, 0 ≤ qG i j) (hG1 : ∀ i j, qG i j ≤ 1-ζ)
    (hBsym : ∀ i j, qB i j = qB j i) (hGsym : ∀ i j, qG i j = qG j i)
    (hdiag : ∀ i, 1-ξ ≤ p i+qB i i+qG i i)
    (hoff : ∀ i j, i ≠ j → 1-ξ ≤ qB i j+qG i j)
    (hc : ∀ i : Fin m, α i.castSucc*sqrt (-log (1-p i)) ≤ beta-ζ)
    (hEB : sqrt (Optimization.energy α (fillMatrix qB)) ≤ beta-ζ)
    (hEG : sqrt (Optimization.energy α (fillMatrix qG)) ≤ beta-ζ) : False := by
  let pfull : Fin (m+1) → ℝ := Fin.lastCases 0 p
  have hb : 0 ≤ beta-ζ := by have hh := beta_pos; linarith
  have hpf0 : ∀ i, 0 ≤ pfull i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [pfull]
    · simpa only [pfull,Fin.lastCases_castSucc] using hp0 i
  have hpf1 : ∀ i, pfull i ≤ 1-ζ := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [pfull,Fin.lastCases_last]
      linarith
    · simpa only [pfull,Fin.lastCases_castSucc] using hp1 i
  have hfill0 : ∀ q : Fin m → Fin m → ℝ, (∀ i j, 0 ≤ q i j) →
      ∀ i j, 0 ≤ fillMatrix q i j := by
    intro q hq i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩ | rfl <;> simp [hq]
  have hfill1 : ∀ q : Fin m → Fin m → ℝ, (∀ i j, q i j ≤ 1-ζ) →
      ∀ i j, fillMatrix q i j ≤ 1-ζ := by
    intro q hq i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩ | rfl
    · simpa only [fillMatrix_active] using hq i j
    all_goals simp only [fillMatrix_last_left,fillMatrix_last_right]; linarith
  apply hopt (m+1) (by omega) (by exact_mod_cast hcount) α pfull (fillMatrix qB) (fillMatrix qG)
    hα hsum hpf0 hpf1 (hfill0 qB hB0) (hfill1 qB hB1)
    (hfill0 qG hG0) (hfill1 qG hG1) (fillMatrix_symm qB hBsym) (fillMatrix_symm qG hGsym)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [pfull,Fin.lastCases_last,fillMatrix_last_left]
      linarith
    · simpa only [pfull,Fin.lastCases_castSucc,fillMatrix_active] using hdiag i
  · intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩ | rfl
    · simpa only [fillMatrix_active] using hoff i j (fun h => hij (congrArg Fin.castSucc h))
    all_goals simp only [fillMatrix_last_left,fillMatrix_last_right]; linarith
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [pfull,Fin.lastCases_last,sub_zero,log_one,neg_zero,sqrt_zero,mul_zero] using hb
    · simpa only [pfull,Fin.lastCases_castSucc] using hc i
  · simpa only [←Optimization.energy_eq_neg_sum] using hEB
  · simpa only [←Optimization.energy_eq_neg_sum] using hEG

end HadwigerRamsey.Main
