import HadwigerRamsey.ThomasonUpper.PartitionFailure

open scoped BigOperators Classical Topology
open Finset Real Filter

namespace HadwigerRamsey.ThomasonUpper

/-- Uniformly in the class counts and densities, a fixed quadratic
entropy margin absorbs the linear prefactor in P. The order threshold
depends only on the displayed constants, not on the graph or its partition. -/
theorem eventually_partitionFailure_small {tau omega phi C delta : ℝ} (K : ℕ)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (homega : 1 ≤ omega)
    (hC : 0 < C) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ K →
      ∀ ell : Fin k → ℕ, ∀ q : Fin k → Fin k → ℝ,
      (∀ i j, 0 ≤ q i j) → ∀ L : ℕ, 0 < L → (∑ i, ell i) = L →
      (L : ℝ) ≤ C*sqrt (log (n : ℝ)) →
      (1+delta)*log (n : ℝ) ≤ (L : ℝ)^2*
        (regularizedLambda (fun i => (ell i : ℝ)/L) q tau + phi*log tau) →
      partitionFailure ell q tau omega phi ≤ (n : ℝ)^(-(1+delta/2)) := by
  let A := log (2*omega)-(K : ℝ)*log tau
  have hlogtau : log tau ≤ 0 := log_nonpos htau.le htau1
  have hlogomega : 0 ≤ log (2*omega) := log_nonneg (by linarith)
  have hA : 0 ≤ A := by
    dsimp only [A]
    nlinarith [show (0 : ℝ) ≤ K by positivity]
  have htop : Tendsto (fun n : ℕ => sqrt (log (n : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [htop.eventually_ge_atTop (2*C*A/delta),
    (eventually_ge_atTop 2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n)] with n hsqrt hn
  intro k hk ell q hq L hL hsum hupper hquad
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 ≤ log (n : ℝ) := (log_pos hnR).le
  have hroot := sqrt_nonneg (log (n : ℝ))
  have hrootSq := sq_sqrt hlogn
  have hsmall : C*A*sqrt (log (n : ℝ)) ≤ (delta/2)*log (n : ℝ) := by
    have hh := (div_le_iff₀ hdelta).mp hsqrt
    nlinarith [mul_nonneg hroot (sub_nonneg.mpr hh)]
  have hkR : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hcoeff : log (2*omega)-(k : ℝ)*log tau ≤ A := by
    dsimp only [A]
    nlinarith
  have hLnonneg : (0 : ℝ) ≤ L := by positivity
  have hlinear : (L : ℝ)*(log (2*omega)-(k : ℝ)*log tau) ≤
      C*A*sqrt (log (n : ℝ)) := by
    calc
      _ ≤ (L : ℝ)*A := mul_le_mul_of_nonneg_left hcoeff hLnonneg
      _ ≤ (C*sqrt (log (n : ℝ)))*A := mul_le_mul_of_nonneg_right hupper hA
      _ = _ := by ring
  have hPpos := partitionFailure_pos ell q (phi := phi) htau (by linarith : 0 < omega) hq
  apply (log_le_log_iff hPpos (rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _)).mp
  rw [log_partitionFailure ell q hL hsum htau (by linarith) hq,
    log_rpow (by linarith : (0 : ℝ) < n)]
  nlinarith

/-- The rounded choice L >= (1+gamma)*sqrt(x/Lambda) gives the
quadratic margin needed above, after reserving 2*xi*Lambda for deletion and regularization
and another xi*Lambda for the phi*log(1/tau) cost. -/
theorem rounded_quadratic_entropy_margin {Lambda R tau phi gamma xi delta x : ℝ}
    {L : ℕ} (hLambda : 0 < Lambda) (hx : 0 ≤ x) (hgamma : 0 ≤ gamma)
    (hxi : 3*xi ≤ 1)
    (hround : (1+gamma)*sqrt (x/Lambda) ≤ (L : ℝ))
    (hreg : (1-2*xi)*Lambda ≤ R)
    (hphi : phi*(-log tau) ≤ xi*Lambda)
    (hgap : 1+delta ≤ (1+gamma)^2*(1-3*xi)) :
    (1+delta)*x ≤ (L : ℝ)^2*(R+phi*log tau) := by
  have hc : 0 ≤ 1-3*xi := by linarith
  have hnet : (1-3*xi)*Lambda ≤ R+phi*log tau := by nlinarith
  have hsqrt := sq_sqrt (div_nonneg hx hLambda.le)
  have hleft : 0 ≤ (1+gamma)*sqrt (x/Lambda) :=
    mul_nonneg (by linarith) (sqrt_nonneg _)
  have hLsq : (1+gamma)^2*(x/Lambda) ≤ (L : ℝ)^2 := by
    have hh := (sq_le_sq₀ hleft (show (0 : ℝ) ≤ L by positivity)).mpr hround
    simpa only [mul_pow,hsqrt] using hh
  have hcancel : ((1+gamma)^2*(x/Lambda))*((1-3*xi)*Lambda) =
      (1+gamma)^2*(1-3*xi)*x := by field_simp
  have hscaled := mul_le_mul_of_nonneg_right hLsq (mul_nonneg hc hLambda.le)
  rw [hcancel] at hscaled
  exact (mul_le_mul_of_nonneg_right hgap hx).trans
    (hscaled.trans (mul_le_mul_of_nonneg_left hnet (sq_nonneg (L : ℝ))))

/-- The defective-pair deletion term is uniformly negligible relative
to s when P <= n^(-1-xi) and s <= n. -/
theorem eventually_defective_pair_loss_small {xi eta : ℝ} (hxi : 0 < xi) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n → ∀ P : ℝ, 0 ≤ P →
      P ≤ (n : ℝ)^(-(1+xi)) → 4*(s : ℝ)*P ≤ eta/2 := by
  have ht := (tendsto_rpow_neg_atTop hxi).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := ht.eventually (gt_mem_nhds (show (0 : ℝ) < eta/8 by positivity))
  filter_upwards [hsmall,(eventually_ge_atTop 1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n)] with n hn hnpos
  intro s hs P hP hbound
  change (n : ℝ)^(-xi) < eta/8 at hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsR : (s : ℝ) ≤ n := by exact_mod_cast hs
  have heq : (n : ℝ)*(n : ℝ)^(-(1+xi)) = (n : ℝ)^(-xi) := by
    calc
      _ = (n : ℝ)^(1 : ℝ)*(n : ℝ)^(-(1+xi)) := by rw [rpow_one]
      _ = (n : ℝ)^(1+(-(1+xi))) := (rpow_add hnR _ _).symm
      _ = _ := by congr 1; ring
  have hh : (s : ℝ)*P ≤ (n : ℝ)^(-xi) := by
    calc
      _ ≤ (n : ℝ)*P := mul_le_mul_of_nonneg_right hsR hP
      _ ≤ (n : ℝ)*(n : ℝ)^(-(1+xi)) := mul_le_mul_of_nonneg_left hbound hnR.le
      _ = _ := heq
  nlinarith

end HadwigerRamsey.ThomasonUpper
