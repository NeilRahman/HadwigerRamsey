import HadwigerRamsey.Existence.Even
import HadwigerRamsey.Decomposition

open scoped Classical
open Real
namespace HadwigerRamsey
set_option maxHeartbeats 600000

/-- Theorem 1.2, for every sufficiently large integer order. -/
theorem existencethm (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : Fin 3 → SimpleGraph (Fin n),
      IsThreeDecomposition G ∧
      ∀ i, (hadwigerNumber (G i) : ℝ) ≤ (1+epsilon)*beta*n/sqrt (log (n : ℝ)) := by
  have hb0 := beta_pos
  obtain ⟨M,hM⟩ := Existence.even_construction (epsilon/2) (by positivity)
  refine ⟨max (2*M+2) (max 3 ⌈(2+epsilon)/epsilon⌉₊),?_⟩
  intro n hn
  have hnM : 2*M+2 ≤ n := (le_max_left _ _).trans hn
  have hn3 : 3 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnceil : ⌈(2+epsilon)/epsilon⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  let m := (n+1)/2
  have hmM : M ≤ m := by dsimp [m]; omega
  have hn2m : n ≤ 2*m := by dsimp [m]; omega
  have hmupper : 2*m ≤ n+1 := by dsimp [m]; omega
  obtain ⟨ω,hω⟩ := hM m hmM
  let f : Fin n → Fin (2*m) := Fin.castLE hn2m
  let G := fun i : Fin 3 => (Existence.colourGraph (Existence.label i) ω).comap f
  refine ⟨G,(Existence.colourGraph_decomposition ω).comap f (Fin.castLE_injective hn2m),?_⟩
  intro i
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith only [hnR]
  have hroot : 0 < sqrt (log (n : ℝ)) := sqrt_pos.mpr (log_pos (by linarith only [hnR]))
  have hNpos : (0 : ℝ) < 2*(m : ℝ) := by
    have hh : (n : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hn2m
    linarith only [hnpos,hh]
  have hlog := log_le_log hnpos (show (n : ℝ) ≤ 2*(m : ℝ) by exact_mod_cast hn2m)
  have hroots := sqrt_le_sqrt hlog
  have horder : (1+epsilon/2)*(2*(m : ℝ)) ≤ (1+epsilon)*n := by
    have hh : (2+epsilon)/epsilon ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnceil)
    have hh' := (div_le_iff₀ hepsilon).mp hh
    have hNu : 2*(m : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hmupper
    have hh'' := mul_le_mul_of_nonneg_left hNu (show 0 ≤ 1+epsilon/2 by positivity)
    nlinarith only [hh',hh'']
  have hminor : hadwigerNumber (G i) ≤ hadwigerNumber (Existence.colourGraph (Existence.label i) ω) :=
    hadwigerNumber_comap_le _ f (Fin.castLE_injective hn2m)
  calc
    (hadwigerNumber (G i) : ℝ) ≤ hadwigerNumber (Existence.colourGraph (Existence.label i) ω) := by exact_mod_cast hminor
    _ ≤ (1+epsilon/2)*beta*(2*m)/sqrt (log (2*(m : ℝ))) := hω _
    _ ≤ (1+epsilon/2)*beta*(2*m)/sqrt (log (n : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) hroot hroots
    _ ≤ (1+epsilon)*beta*n/sqrt (log (n : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hroot.le
      nlinarith only [mul_le_mul_of_nonneg_right horder beta_pos.le]
end HadwigerRamsey
