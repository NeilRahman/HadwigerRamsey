import HadwigerRamsey.Main.DensityCaps
import HadwigerRamsey.Opt

open scoped Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.Main

/-- A uniformly small Hadwiger number caps every sufficiently large internal
or bipartite density. The witnesses are those supplied by Lemmas 3.3 and 3.5. -/
theorem set_density_caps {n NB ND : ℕ} (G : SimpleGraph (Fin n))
    {lam ζ γD γB : ℝ} (hlam : 0 < lam) (hζD : ζ ≤ γD) (hζB : ζ ≤ γB)
    (hcut : ((max ND NB+2 : ℕ) : ℝ) ≤ lam/2*n)
    (hdense : ∀ m ≥ ND, ∀ H : SimpleGraph (Fin m),
      (1-γD)*(m.choose 2 : ℝ) ≤ H.edgeFinset.card →
      (2*beta/lam)*m/sqrt (log (m : ℝ)) ≤ (hadwigerNumber H : ℝ))
    (hbip : ∀ m : ℕ, ∀ H : SimpleGraph (Fin m), ∀ X Y : Finset (Fin m),
      H.IsBipartiteWith (X : Set (Fin m)) (Y : Set (Fin m)) →
      X ∪ Y = univ → X.card = Y.card → NB ≤ X.card →
      (1-γB)*(X.card : ℝ)^2 ≤ H.edgeFinset.card →
      (2*beta/lam)*(X.card : ℝ)/sqrt (log (X.card : ℝ)) ≤ (hadwigerNumber H : ℝ))
    (hsmall : (hadwigerNumber G : ℝ) < beta*n/sqrt (log (n : ℝ))) :
    (∀ S : Finset (Fin n), lam/2*n ≤ (S.card : ℝ) →
      internalDensity G S ≤ 1-ζ) ∧
    (∀ S T : Finset (Fin n), Disjoint S T →
      lam/2*n ≤ (S.card : ℝ) → lam/2*n ≤ (T.card : ℝ) →
      (G.edgeDensity S T : ℝ) ≤ 1-ζ) := by
  have hK : 0 ≤ 2*beta/lam := by have := beta_pos; positivity
  have hscale : (2*beta/lam)*(lam/2) = beta := by field_simp [hlam.ne']
  have hs : (hadwigerNumber G : ℝ) <
      (2*beta/lam)*(lam/2)*n/sqrt (log (n : ℝ)) := by rw [hscale]; exact hsmall
  constructor
  · intro S hS
    have hNS : max ND NB+2 ≤ S.card := by exact_mod_cast hcut.trans hS
    have hND : ND ≤ S.card := by have := le_max_left ND NB; omega
    have hc := internal_density_cap G S hK hND (by omega) hS hdense hs
    exact hc.le.trans (sub_le_sub_left hζD 1)
  · intro S T hdis hS hT
    have hsize : lam/2*n ≤ ((min S.card T.card : ℕ) : ℝ) := by
      rw [Nat.cast_min]
      exact le_min hS hT
    have hN : max ND NB+2 ≤ min S.card T.card := by exact_mod_cast hcut.trans hsize
    have hNB : NB ≤ min S.card T.card := by have := le_max_right ND NB; omega
    have hc := cross_density_cap G S T hdis hK hNB (by omega) hsize hbip hs
    exact hc.le.trans (sub_le_sub_left hζB 1)

end HadwigerRamsey.Main
