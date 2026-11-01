import HadwigerRamsey.BipMinor.Core
import HadwigerRamsey.BipMinor.Entropy
import HadwigerRamsey.ThomasonUpper
import HadwigerRamsey.ThomasonUpper.FinalScale

open scoped Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.BipMinor
set_option maxHeartbeats 1200000

attribute [-instance] SimpleGraph.instDecidableComapAdj in
/-- The lemma for a balanced two-class vertex map, before the set-based wrapper. -/
theorem balanced_dense_minor (K : ℝ) (hK : 0 < K) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∃ N : ℕ, 0 < N ∧
      ∀ n a : ℕ, N < a → ∀ G : SimpleGraph (Fin n), ∀ c : Fin n → Fin 2,
      (∀ u v, G.Adj u v → c u ≠ c v) →
      (∀ i, (classVertices c i).card = a) →
      (1-gamma)*(a : ℝ)^2 ≤ G.edgeFinset.card →
      K*(a : ℝ)/sqrt (log (a : ℝ)) ≤ (hadwigerNumber G : ℝ) := by
  let epsilon := min (1/100) (exp (-((32*(K+1))^2)))
  have he : 0 < epsilon := by dsimp only [epsilon]; positivity
  have he100 : epsilon ≤ 1/100 := min_le_left _ _
  have he1 : epsilon ≤ 1 := by linarith only [he100]
  have hlog : (32*(K+1))^2 ≤ -log epsilon := by
    have hh := log_le_log he (min_le_right (1/100) (exp (-((32*(K+1))^2))))
    rw [log_exp] at hh
    linarith only [hh]
  let gamma := epsilon/4096
  have hg : 0 < gamma := by dsimp only [gamma]; positivity
  have hgsmall : gamma ≤ 1/128 := by dsimp only [gamma]; linarith only [he100]
  obtain ⟨N,hN⟩ := HadwigerRamsey.thomasonupper epsilon he
  refine ⟨gamma,hg,max N 100,by omega,?_⟩
  intro n a ha G c hp hsize hedges
  have ha100 : 100 ≤ a := by omega
  have haR100 : (100 : ℝ) ≤ a := by exact_mod_cast ha100
  have haR : (0 : ℝ) < a := by linarith only [haR100]
  obtain ⟨Z,hZn,hlo,hhi,hproper,hcard,hdegree,hmass,hcross⟩ := exists_core G c ha100 hp hsize hg.le hgsmall hedges
  let M := n-Z.card
  let H := restrictedGraph G Z
  let classes := restrictedClasses c Z
  have hMp : 0 < M := by dsimp only [M]; omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMp
  have hc := connected_quarter H classes (by omega : 0 < a) hlo hproper hcard hdegree
  have hdκ : a/4 ≤ vertexConnectivity H := (vertexConnectedAtLeast_iff hMp H _).mp hc
  have hdiv : a ≤ 8*(a/4) := by omega
  have hconn : epsilon*(M : ℝ) ≤ vertexConnectivity H := by
    have hdivR : (a : ℝ) ≤ 8*((a/4 : ℕ) : ℝ) := by exact_mod_cast hdiv
    have hdκR : ((a/4 : ℕ) : ℝ) ≤ vertexConnectivity H := by exact_mod_cast hdκ
    have hhiR : (M : ℝ) ≤ 2*(a : ℝ) := by exact_mod_cast hhi
    have hh := mul_le_mul_of_nonneg_right he100 hMr.le
    nlinarith only [hdivR,hdκR,hhiR,hh]
  have hcapped : 1-epsilon ≤ blockDensity H classes 0 1 := by
    dsimp only [gamma] at hcross
    linarith only [hcross,he]
  have hLambda := entropy_lower H classes he he1 hmass hcapped
  have hLambda0 : 0 ≤ cappedLambda H classes epsilon := cappedLambda_nonneg H classes he he1
  have hrootLambda : 8*(K+1) ≤ sqrt (cappedLambda H classes epsilon) := by
    apply le_sqrt_of_sq_le
    nlinarith only [hLambda,hlog]
  have hgain : 2*K ≤ sqrt (cappedLambda H classes epsilon)-epsilon := by
    linarith only [hrootLambda,he100,hK]
  have hbound := hN M (by dsimp only [M]; omega) H hconn 2 classes
    (fun i => le_trans (by linarith only [he100]) (hmass i))
  have hmMinor : hadwigerNumber H ≤ hadwigerNumber G := hadwigerNumber_comap_le G _ (survivorMap_injective Z)
  have hmMinorR : (hadwigerNumber H : ℝ) ≤ hadwigerNumber G := by exact_mod_cast hmMinor
  obtain ⟨hrootA,hrootAM,hrootMA⟩ := sqrt_log_order_comparison (by omega : 2 ≤ a) hlo hhi
  have hrootM : 0 < sqrt (log (M : ℝ)) := hrootA.trans_le hrootAM
  have hscale : (a : ℝ)/(2*sqrt (log (a : ℝ))) ≤ (M : ℝ)/sqrt (log (M : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) hrootM).mpr
    have hloR : (a : ℝ) ≤ M := by exact_mod_cast hlo
    have hh := mul_le_mul_of_nonneg_left hrootMA haR.le
    have hh' := mul_le_mul_of_nonneg_right hloR hrootA.le
    nlinarith only [hh,hh']
  have hpos : 0 ≤ (M : ℝ)/sqrt (log (M : ℝ)) := by positivity
  have hh := mul_le_mul hscale hgain (by linarith only [hK] : 0 ≤ 2*K) hpos
  have htarget : K*(a : ℝ)/sqrt (log (a : ℝ)) ≤ (hadwigerNumber H : ℝ) := by
    calc
      _ = ((a : ℝ)/(2*sqrt (log (a : ℝ))))*(2*K) := by ring
      _ ≤ _ := hh
      _ ≤ _ := hbound
  exact htarget.trans hmMinorR
end HadwigerRamsey.BipMinor
