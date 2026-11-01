import HadwigerRamsey.ThomasonUpper.MultitypeFinite
import HadwigerRamsey.ThomasonUpper.PartitionFailureAsymptotic

open scoped BigOperators Classical Topology
open Finset Real Filter

namespace HadwigerRamsey.ThomasonUpper

/-- A uniform many-parts consequence of A.1 for exact-multiple classes.
The quadratic entropy margin is the remaining graph-dependent input:
this theorem discharges P's decay and both losses in the part count. -/
theorem multitype_many_parts_of_entropy_margin {tau omega phi C delta eta : ℝ} (K : ℕ)
    (htau : 0 < tau) (htau1 : tau < 1) (homega : 1 ≤ omega)
    (hphi : 0 < phi) (hphi1 : phi < 1) (hC : 0 < C)
    (hdelta : 0 < delta) (heta : 0 < eta) (hcost : 4/(omega*phi) ≤ eta/2) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k ≤ K →
      ∀ G : SimpleGraph (Fin n), ∀ classes : Fin n → Fin k,
      ∀ ell : Fin k → ℕ, ∀ s : ℕ, 2 ≤ s →
      (∀ i, 1 ≤ ell i) → (∀ i, (classVertices classes i).card = s*ell i) →
      ∀ L : ℕ, 0 < L → (∑ i, ell i) = L →
      (L : ℝ) ≤ C*sqrt (log (n : ℝ)) →
      (1+delta)*log (n : ℝ) ≤ (L : ℝ)^2*
        (regularizedLambda (fun i => (ell i : ℝ)/L)
          (fun i j => 1-blockDensity G classes i j) tau + phi*log tau) →
      ∃ m : ℕ, ∃ U : Fin m → Finset (Fin n), 0 < m ∧ m ≤ s ∧
        (1-eta)*(s : ℝ) ≤ m ∧ IsCompleteEquipartition G U := by
  have hfailure := eventually_partitionFailure_small (phi := phi) K htau htau1.le homega hC hdelta
  have hloss := eventually_defective_pair_loss_small (show 0 < delta/2 by positivity) heta
  filter_upwards [hfailure,hloss] with n hfailure hloss
  intro k hk hkK G classes ell s hs hell hcard L hL hsum hupper hquad
  let q := fun i j => 1-blockDensity G classes i j
  let P := partitionFailure ell q tau omega phi
  have hq : ∀ i j, 0 ≤ q i j := fun i j => sub_nonneg.mpr (blockDensity_le_one G classes i j)
  have hPpos : 0 < P := partitionFailure_pos ell q htau (by linarith) hq
  have hPbound : P ≤ (n : ℝ)^(-(1+delta/2)) :=
    hfailure k hkK ell q hq L hL hsum hupper hquad
  have hsn : s ≤ n := by
    let i : Fin k := ⟨0,hk⟩
    have hc : (classVertices classes i).card ≤ n := by simpa using card_le_univ (classVertices classes i)
    have hi := hcard i
    have he := hell i
    nlinarith
  have hdeleted := hloss s hsn P hPpos.le hPbound
  obtain ⟨m,U,hm,hms,hlower,hU⟩ := multitype_complete_equipartition G classes ell hk hs hell hcard
    htau htau1 homega hphi hphi1
  change (s : ℝ)-4*s/(omega*phi)-4*(s : ℝ)^2*P ≤ m at hlower
  have hsR : (0 : ℝ) ≤ s := by positivity
  have hfirst : 4*(s : ℝ)/(omega*phi) ≤ (eta/2)*s := by
    calc
      _ = (4/(omega*phi))*(s : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcost hsR
  have hsecond : 4*(s : ℝ)^2*P ≤ (eta/2)*s := by
    have hh := mul_le_mul_of_nonneg_right hdeleted hsR
    nlinarith
  refine ⟨m,U,hm,hms,?_,hU⟩
  nlinarith

/-- The same consequence using the original graph order as the probability
scale for a smaller induced graph. This avoids changing logarithmic scales
when trimming the classes in A.3. -/
theorem multitype_many_parts_at_ambient_order {tau omega phi C delta eta : ℝ} (K : ℕ)
    (htau : 0 < tau) (htau1 : tau < 1) (homega : 1 ≤ omega)
    (hphi : 0 < phi) (hphi1 : phi < 1) (hC : 0 < C)
    (hdelta : 0 < delta) (heta : 0 < eta) (hcost : 4/(omega*phi) ≤ eta/2) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k ≤ K →
      ∀ N : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin N), ∀ classes : Fin N → Fin k,
      ∀ ell : Fin k → ℕ, ∀ s : ℕ, 2 ≤ s →
      (∀ i, 1 ≤ ell i) → (∀ i, (classVertices classes i).card = s*ell i) →
      ∀ L : ℕ, 0 < L → (∑ i, ell i) = L →
      (L : ℝ) ≤ C*sqrt (log (n : ℝ)) →
      (1+delta)*log (n : ℝ) ≤ (L : ℝ)^2*
        (regularizedLambda (fun i => (ell i : ℝ)/L)
          (fun i j => 1-blockDensity G classes i j) tau + phi*log tau) →
      ∃ m : ℕ, ∃ U : Fin m → Finset (Fin N), 0 < m ∧ m ≤ s ∧
        (1-eta)*(s : ℝ) ≤ m ∧ IsCompleteEquipartition G U := by
  have hfailure := eventually_partitionFailure_small (phi := phi) K htau htau1.le homega hC hdelta
  have hloss := eventually_defective_pair_loss_small (show 0 < delta/2 by positivity) heta
  filter_upwards [hfailure,hloss] with n hfailure hloss
  intro k hk hkK N hN G classes ell s hs hell hcard L hL hsum hupper hquad
  let q := fun i j => 1-blockDensity G classes i j
  let P := partitionFailure ell q tau omega phi
  have hq : ∀ i j, 0 ≤ q i j := fun i j => sub_nonneg.mpr (blockDensity_le_one G classes i j)
  have hPpos : 0 < P := partitionFailure_pos ell q htau (by linarith) hq
  have hPbound : P ≤ (n : ℝ)^(-(1+delta/2)) :=
    hfailure k hkK ell q hq L hL hsum hupper hquad
  have hsn : s ≤ n := by
    let i : Fin k := ⟨0,hk⟩
    have hc : (classVertices classes i).card ≤ N := by simpa using card_le_univ (classVertices classes i)
    have hi := hcard i
    have he := hell i
    nlinarith
  have hdeleted := hloss s hsn P hPpos.le hPbound
  obtain ⟨m,U,hm,hms,hlower,hU⟩ := multitype_complete_equipartition G classes ell hk hs hell hcard
    htau htau1 homega hphi hphi1
  change (s : ℝ)-4*s/(omega*phi)-4*(s : ℝ)^2*P ≤ m at hlower
  have hsR : (0 : ℝ) ≤ s := by positivity
  have hfirst : 4*(s : ℝ)/(omega*phi) ≤ (eta/2)*s := by
    calc
      _ = (4/(omega*phi))*(s : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcost hsR
  have hsecond : 4*(s : ℝ)^2*P ≤ (eta/2)*s := by
    have hh := mul_le_mul_of_nonneg_right hdeleted hsR
    nlinarith
  refine ⟨m,U,hm,hms,?_,hU⟩
  nlinarith

end HadwigerRamsey.ThomasonUpper
