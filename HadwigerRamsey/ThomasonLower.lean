import HadwigerRamsey.Asymptotic
import HadwigerRamsey.Blocks
import HadwigerRamsey.Measurability

open scoped BigOperators
open Finset Set MeasureTheory ProbabilityTheory Real
namespace HadwigerRamsey

/-- Theorem 1.4 (`thomasonlower`). The class map `τ` represents the vertex
partition. The probability space is arbitrary: the hypotheses state exactly
that its undirected edge events are measurable, mutually independent, and
have the prescribed probabilities. The cutoff is uniform in the number of
classes, their sizes, the probability matrix, and the probability space. -/
theorem thomasonlower (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : ℕ, ∀ τ : Fin n → Fin k,
      ∀ p : Fin k → Fin k → ℝ,
      (∀ i j, p i j = p j i) →
      (∀ i j, 0 ≤ p i j) →
      (∀ i j, p i j ≤ 1-ε) →
      sqrt (blockLambda τ p) > ε →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (G : Ω → SimpleGraph (Fin n)),
      (∀ e, MeasurableSet (edgeEvent G e)) →
      iIndepSet (edgeEvent G) μ →
      (∀ e : Edge n, μ.real (edgeEvent G e) = p (τ e.val.1) (τ e.val.2)) →
      1-ε ≤ μ.real {ω | (hadwigerNumber (G ω) : ℝ) ≤
        (1+ε)*sqrt (blockLambda τ p)*(n : ℝ)/sqrt (log n)} := by
  classical
  by_cases hε1 : ε < 1
  · let B := -log ε
    have hB : 0 ≤ B := by dsimp [B]; have := log_nonpos hε.le hε1.le; linarith
    obtain ⟨N,hN⟩ := uniform_tail_bound ε B hε hB
    refine ⟨max 2 N, ?_⟩
    intro n hn k τ p hsym hp0 hpe hL Ω mΩ μ hμ G hA hind hp
    have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    let Λ := blockLambda τ p
    let w : Fin n → Fin n → ℝ := fun u v => -log (1-p (τ u) (τ v))
    have hw : ∀ u v, 0 ≤ w u v := fun u v => (log_weight_bounds hε (hp0 _ _) (hpe _ _)).1
    have hwB : ∀ u v, w u v ≤ B := fun u v => (log_weight_bounds hε (hp0 _ _) (hpe _ _)).2
    have hwsym : ∀ u v, w u v = w v u := by intro u v; dsimp [w]; rw [hsym]
    have hid : (n : ℝ)^2*Λ = ∑ u, ∑ v, w u v := blockLambda_identity hn0 τ p
    have hΛ0 : 0 ≤ Λ := (sqrt_pos.mp (hε.trans hL)).le
    have hΛε : ε^2 ≤ Λ := by nlinarith only [sq_sqrt hΛ0, hL, hε]
    have hΛB : Λ ≤ B := by
      have hsum : (∑ u, ∑ v, w u v) ≤ (n : ℝ)^2*B := by
        calc
          _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, B := Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hwB u v))
          _ = _ := by simp; ring
      rw [← hid] at hsum
      exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hnR)).mp hsum
    obtain ⟨hs, hsN, htail⟩ := hN n ((le_max_right _ _).trans hn) Λ hΛε hΛB
    let R := (1+ε)*(n : ℝ)*sqrt Λ/sqrt (log n)
    let s := ⌈R⌉₊
    have hs2 : 2 ≤ s := hs
    have hwedge : ∀ e : Edge n, 0 ≤ w e.val.1 e.val.2 := fun e => hw _ _
    have hweight : ∑ e : Edge n, w e.val.1 e.val.2 ≤ (n : ℝ)^2*Λ/2 := by
      rw [hid]
      exact total_weight_le w hwsym hw
    have hprob : ∀ e : Edge n, μ.real (edgeEvent G e)ᶜ = exp (-w e.val.1 e.val.2) := by
      intro e
      have hc := measureReal_add_measureReal_compl (μ := μ) (hA e)
      simp only [measureReal_univ_eq_one, hp e] at hc
      have hpos : 0 < 1-p (τ e.val.1) (τ e.val.2) := by linarith [hpe (τ e.val.1) (τ e.val.2)]
      dsimp [w]
      rw [neg_neg, exp_log hpos]
      linarith
    have hfinite := finite_minor_bound G hs2 (fun e => w e.val.1 e.val.2)
      hwedge hA hind hprob hweight
    have htail' : μ.real {ω | HasCliqueMinor (G ω) s} ≤ ε := by
      apply hfinite.trans
      have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
      have hss : (s : ℝ)*((s : ℝ)-1) ≠ 0 := by
        have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs2
        nlinarith
      have heq : (s : ℝ)^n * exp (-(Fintype.card (Edge s) : ℝ) *
          exp (-((n : ℝ)^2*Λ/2) / (Fintype.card (Edge s) : ℝ))) = tailBound n s Λ := by
        rw [edge_card_real]
        have hquot : -((n : ℝ)^2*Λ/2) / ((s : ℝ)*((s : ℝ)-1)/2) =
            -((n : ℝ)^2*Λ) / ((s : ℝ)*((s : ℝ)-1)) := by field_simp
        rw [hquot]
        dsimp [tailBound]
        rw [exp_sub, exp_nat_mul, exp_log hspos]
        simp only [neg_mul, exp_neg, div_eq_mul_inv]
      rw [heq]
      exact htail
    have hmeas := measurableSet_graph_property G hA (fun H => HasCliqueMinor H s)
    have hc := measureReal_add_measureReal_compl (μ := μ) hmeas
    simp only [measureReal_univ_eq_one] at hc
    have hgood : {ω | HasCliqueMinor (G ω) s}ᶜ ⊆
        {ω | (hadwigerNumber (G ω) : ℝ) ≤ (1+ε)*sqrt (blockLambda τ p)*(n : ℝ)/sqrt (log n)} := by
      intro ω hω
      have hh := hadwigerNumber_lt_of_no_minor (by omega : 0 < s) hω
      have hhR : (hadwigerNumber (G ω) : ℝ) < R := by
        have hh' : (hadwigerNumber (G ω) : ℝ)+1 ≤ s := by exact_mod_cast hh
        have hceil : (s : ℝ) < R+1 := Nat.ceil_lt_add_one (by dsimp [R]; positivity)
        linarith
      have hRe : R = (1+ε)*sqrt (blockLambda τ p)*(n : ℝ)/sqrt (log n) := by dsimp [R,Λ]; ring
      rw [← hRe]
      exact hhR.le
    exact (show 1-ε ≤ μ.real {ω | HasCliqueMinor (G ω) s}ᶜ by linarith).trans (measureReal_mono hgood)
  · refine ⟨2, ?_⟩
    intro n hn k τ p hsym hp0 hpe hL Ω mΩ μ hμ G hA hind hp
    exact le_trans (by linarith) measureReal_nonneg

end HadwigerRamsey
