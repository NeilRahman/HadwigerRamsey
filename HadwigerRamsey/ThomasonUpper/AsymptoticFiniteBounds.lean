import HadwigerRamsey.ThomasonUpper.CompleteEquipartition
import HadwigerRamsey.ThomasonUpper.Density

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

set_option maxHeartbeats 50000

theorem blockLambda_le_complement_bound {n k : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (classes : Fin n → Fin k) {a : ℝ}
    (ha : 0 < a) (hq : ∀ i j, a ≤ 1-blockDensity G classes i j) :
    blockLambda classes (blockDensity G classes) ≤ log (1/a) := by
  have hsum := sum_classMass hn classes
  calc
    _ ≤ ∑ i, ∑ j, classMass classes i*classMass classes j*(-log a) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (neg_le_neg (log_le_log ha (hq i j)))
        (mul_nonneg (classMass_nonneg _ _) (classMass_nonneg _ _))
    _ = -log a := by simp_rw [mul_assoc,← mul_sum,← sum_mul,hsum,one_mul]
    _ = _ := by rw [one_div,log_inv]

theorem part_count_from_trimmed_scale {c eta gamma d T : ℝ} {n s L m : ℕ}
    (hc : 0 < c) (heta : 0 < eta) (heta1 : eta < 1) (hd : d < 1) (hT : 0 < T)
    (hgain : 4 ≤ (c-(1-eta)*(1+gamma))*T)
    (hcost : 4*c*d ≤ c-(1-eta)*(1+gamma))
    (hceil : (L : ℝ) < (1+gamma)*T+1)
    (hretain : (1-d)*(n : ℝ) ≤ (s : ℝ)*L)
    (hm : c*(s : ℝ) ≤ m) : (1-eta)*(n : ℝ)/T ≤ m := by
  have hbud : (1-eta)*(L : ℝ) ≤ c*(1-d)*T := by
    have hh := mul_le_mul_of_nonneg_right hcost hT.le
    have hh' := mul_lt_mul_of_pos_left hceil (show 0 < 1-eta by linarith)
    nlinarith
  have hchain : (1-d)*((1-eta)*(n : ℝ)) ≤ (1-d)*((m : ℝ)*T) := by
    calc
      _ = (1-eta)*((1-d)*(n : ℝ)) := by ring
      _ ≤ (1-eta)*((s : ℝ)*L) := mul_le_mul_of_nonneg_left hretain (by linarith)
      _ = (s : ℝ)*((1-eta)*L) := by ring
      _ ≤ (s : ℝ)*(c*(1-d)*T) := mul_le_mul_of_nonneg_left hbud (by positivity)
      _ = (1-d)*T*(c*(s : ℝ)) := by ring
      _ ≤ (1-d)*T*m := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  have hh := (mul_le_mul_iff_right₀ (show 0 < 1-d by linarith)).mp hchain
  exact (div_le_iff₀ hT).mpr hh

theorem part_size_from_many_parts {N m s L : ℕ} {G : SimpleGraph (Fin N)}
    {W : Fin m → Finset (Fin N)} (hW : IsCompleteEquipartition G W)
    (hs : 0 < s) (hN : N = s*L) {c : ℝ} (hc : 0 < c) (hm : c*(s : ℝ) ≤ m)
    (i : Fin m) : ((W i).card : ℝ) ≤ (L : ℝ)/c+1 := by
  have hnon : (1 : ℝ) ≤ (W i).card := by
    have hh : 1 ≤ (W i).card := (hW.nonempty i).card_pos
    exact_mod_cast hh
  have hsum : (m : ℝ)*((W i).card-1) ≤ N := by
    have hh := sum_le_sum (s := (univ : Finset (Fin m))) (fun j _ =>
      show ((W i).card : ℝ)-1 ≤ (W j).card from by
        have hb : ((W i).card : ℝ) ≤ (W j).card+1 := by exact_mod_cast hW.balanced i j
        linarith)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,← Nat.cast_sum,hW.sum_card] at hh
    exact hh
  have hmul := mul_le_mul_of_nonneg_right hm (show 0 ≤ ((W i).card : ℝ)-1 by linarith)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hNR : (N : ℝ) = (s : ℝ)*L := by exact_mod_cast hN
  have hh : c*(((W i).card : ℝ)-1) ≤ L := by nlinarith
  have hd := (le_div_iff₀ hc).mpr (show (((W i).card : ℝ)-1)*c ≤ L by nlinarith)
  linarith

end HadwigerRamsey.ThomasonUpper
