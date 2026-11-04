import HadwigerRamsey.Main.Partition
import HadwigerRamsey.Main.Numerics
import HadwigerRamsey.Main.Entropy
import HadwigerRamsey.Main.Sparse

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper HadwigerRamsey.ControlledPartition
namespace HadwigerRamsey.Main

theorem degenerate_density_small {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) {lam : ℝ} (hlam : 0 < lam)
    (hn : 10 ≤ lam*n) (hsize : 20*lam*n ≤ (S.card : ℝ))
    (hdeg : DegenerateOn G S (3*lam*n)) : internalDensity G S ≤ 31/100 := by
  have ht : (0 : ℝ) < lam*n := by linarith
  have hs : (0 : ℝ) < S.card := by linarith
  have hp := internalDensity_nonneg G S
  have hh := internal_density_weighted G S
  have hd := TwoBigSets.degenerate_ordered G hdeg
  have hprod : internalDensity G S*(S.card : ℝ) ≤ 6*lam*n+1 := by
    by_contra! hb
    have hm := mul_lt_mul_of_pos_right hb hs
    nlinarith only [hh,hd,hm]
  have hm := mul_le_mul_of_nonneg_left hsize hp
  by_contra! hb
  have hm' := mul_lt_mul_of_pos_right hb (show (0:ℝ)<20*lam*n by nlinarith only [ht])
  nlinarith only [hprod,hm,hm',hn]

/-- Condition (c), handling robust pieces and the large degenerate remainder. -/
theorem active_cost_bounds {n N : ℕ} (G : SimpleGraph (Fin n))
    {lam η δ ε θ ζ : ℝ} (D : PartitionData G lam η δ)
    (hn : 0 < n) (hlam : 0 < lam) (hlarge : 10 ≤ lam*n)
    (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθδ : θ ≤ δ)
    (hθζ : θ+ζ ≤ ε*beta) (hz : ζ ≤ beta/100)
    (hthom : ThomasonBound θ N)
    (hN : ∀ i : Fin D.m, N ≤ (D.V i.castSucc).card)
    (hsize : ∀ i : Fin D.m, 2 ≤ (D.V i.castSucc).card)
    (hcap : ∀ i : Fin D.m, internalDensity G (D.V i.castSucc) ≤ 1-θ)
    (hsmall : (hadwigerNumber G : ℝ)*sqrt (log (n : ℝ))/(n : ℝ) ≤ (1-ε)*beta) :
    ∀ i : Fin D.m, ((D.V i.castSucc).card : ℝ)/n *
      sqrt (-log (1-internalDensity G (D.V i.castSucc))) ≤ beta-ζ := by
  intro i
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rcases D.active_kind i with hc | ⟨hd,hs⟩
  · have hSc : ((D.V i.castSucc).card : ℝ) ≤ n := by
      exact_mod_cast (by simpa using (D.V i.castSucc).card_le_univ : (D.V i.castSucc).card ≤ n)
    have hθn := mul_le_mul_of_nonneg_left hSc hθ.le
    have hδn := mul_le_mul_of_nonneg_right hθδ hnR.le
    have hc' : RealConnected G (D.V i.castSucc) (θ*(D.V i.castSucc).card) :=
      hc.mono (hθn.trans hδn)
    have hh := singleton_entropy_upper G hθ hθ1 hthom (D.V i.castSucc)
      (hsize i) (hN i) hc' (hcap i)
    apply connected_cost_gap hε hθζ
    linarith only [hh,hsmall]
  · apply degenerate_cost_bound (internalDensity_nonneg _ _)
      (degenerate_density_small G _ hlam hlarge hs hd)
    · positivity
    · apply (div_le_one hnR).mpr
      exact_mod_cast (by simpa using (D.V i.castSucc).card_le_univ : (D.V i.castSucc).card ≤ n)
    · exact hz

end HadwigerRamsey.Main
