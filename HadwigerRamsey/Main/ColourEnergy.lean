import HadwigerRamsey.Main.Restriction
import HadwigerRamsey.Main.Sparse
import HadwigerRamsey.Main.Numerics

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper HadwigerRamsey.ControlledPartition
namespace HadwigerRamsey.Main

theorem classMass_eq_card {n k : ℕ} (V : Fin k → Finset (Fin n))
    (τ : Fin n → Fin k) (hV : ∀ i, classVertices τ i = V i) (i : Fin k) :
    classMass τ i = ((V i).card : ℝ)/n := by
  change ((classVertices τ i).card : ℝ)/n = _
  rw [hV]

theorem restrictedDensity_univ {n m : ℕ} (G : SimpleGraph (Fin n))
    (V : Fin (m+1) → Finset (Fin n)) (τ : Fin n → Fin (m+1))
    (hV : ∀ i, classVertices τ i = V i) (i j : Fin m) :
    restrictedDensity G V univ i j = blockDensity G τ i.castSucc j.castSucc := by
  unfold restrictedDensity blockDensity
  by_cases hij : i=j
  · subst j
    simp [hV]
  · simp only [if_neg hij,if_neg ((Fin.castSucc_injective m).ne hij),hV,inter_univ]

/-- The sparse-colour estimate in condition (d), including the diagonal correction. -/
theorem sparse_active_energy {n m : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    {e ζ : ℝ} (hz : 0 < ζ) (hz1 : ζ < 1)
    (V : Fin (m+1) → Finset (Fin n)) (τ : Fin n → Fin (m+1))
    (hV : ∀ i, classVertices τ i = V i)
    (hedge : (G.edgeFinset.card : ℝ) ≤ 3*e*(n : ℝ)^2)
    (horder : 1/(n : ℝ) ≤ e)
    (hcap : ∀ i j, restrictedDensity G V univ i j ≤ 1-ζ) :
    Optimization.energy (fun i : Fin m => ((V i.castSucc).card : ℝ)/n)
      (restrictedDensity G V univ) ≤ 7*e*((-log ζ)/(1-ζ)) := by
  let α := fun i : Fin m => ((V i.castSucc).card : ℝ)/n
  let q := restrictedDensity G V univ
  have hf := (capped_log_factor hz hz1).1
  have hc : Optimization.energy α q ≤ ((-log ζ)/(1-ζ)) *
      (∑ i, ∑ j, α i*α j*q i j) := by
    unfold Optimization.energy
    simp only [mul_sum]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    have hh := mul_le_mul_of_nonneg_left
      (logCost_chord hz hz1 (restrictedDensity_nonneg G V univ i j) (hcap i j))
      (show 0 ≤ α i*α j by dsimp [α]; positivity)
    dsimp [Optimization.logCost]
    nlinarith only [hh]
  have hden : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have hweighted := active_weighted_density_upper hn G τ
  have hweighted' : (∑ i, ∑ j, α i*α j*q i j) ≤
      2*(G.edgeFinset.card : ℝ)/(n : ℝ)^2+1/(n : ℝ) := by
    simpa only [α,q,restrictedDensity_univ G V τ hV, classMass_eq_card V τ hV] using hweighted
  have he := div_le_div_of_nonneg_right hedge hden.le
  have he' : 2*(G.edgeFinset.card : ℝ)/(n : ℝ)^2 ≤ 6*e := by
    have hh : (3*e*(n : ℝ)^2)/(n : ℝ)^2 = 3*e := by field_simp
    rw [hh] at he
    calc
      _ = 2*((G.edgeFinset.card : ℝ)/(n : ℝ)^2) := by ring
      _ ≤ 2*(3*e) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  have hsum : (∑ i, ∑ j, α i*α j*q i j) ≤ 7*e := by
    linarith only [hweighted',he',horder]
  have hmul := mul_le_mul_of_nonneg_left hsum hf
  nlinarith only [hc,hmul]

/-- Both alternatives supplied by Lemma 3.6 give the active entropy gap. -/
theorem colour_energy_gap {n m N : ℕ} (G : SimpleGraph (Fin n))
    {ε lam e θ δ₀ ζ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 0 < lam) (hlamsmall : lam ≤ 1/100) (he : 0 ≤ e)
    (helam : e ≤ lam/2) (heε : e ≤ lam*ε/100)
    (hz : 0 < ζ) (hz1 : ζ < 1) (heζ : e ≤ ζ*beta^2/100)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθlam : θ ≤ lam/2)
    (hθδ : θ ≤ δ₀/2) (hθζ : θ ≤ ζ) (hθε : θ ≤ ε*beta/100)
    (hthom : ThomasonBound θ N) (hnN : 2*N ≤ n) (hn4 : 4 ≤ n)
    (horder : 1/(n : ℝ) ≤ e)
    (V : Fin (m+1) → Finset (Fin n)) (τ : Fin n → Fin (m+1))
    (hV : ∀ i, classVertices τ i = V i)
    (hsize : ∀ i : Fin m, lam*n ≤ ((V i.castSucc).card : ℝ))
    (hdummy : ((V (Fin.last m)).card : ℝ) ≤ 21*lam*n)
    (P : Finset (Fin n)) (hP : (1-e)*n ≤ (P.card : ℝ))
    (hgood : ((G.edgeFinset.card : ℝ) ≤ 3*e*(n : ℝ)^2 ∧ P=univ) ∨
      RealConnected G P (δ₀*n))
    (hcap : ∀ i j, restrictedDensity G V P i j ≤ 1-ζ)
    (hhad : (hadwigerNumber G : ℝ)*sqrt (log (n : ℝ))/(n : ℝ) ≤ (1-ε)*beta) :
    Optimization.energy (fun i : Fin m => ((V i.castSucc).card : ℝ)/n)
      (restrictedDensity G V P) ≤ (1-ε/2)*beta^2 := by
  rcases hgood with ⟨hedge,rfl⟩ | hconn
  · exact sparse_energy_gap hε1 hz hz1 heζ
      (sparse_active_energy G (by omega) hz hz1 V τ hV hedge horder hcap)
  · have hh := nearspanning_entropy_upper G hlam hlamsmall he helam hθ hθ1
      hθlam hθδ hthom hnN hn4 V τ hV hsize hdummy P hP hconn
      (fun i j => (hcap i j).trans (by linarith))
    have hratio : e/lam ≤ ε/100 := (div_le_iff₀ hlam).mpr (by nlinarith only [heε])
    apply connected_energy_gap hε hε1 (div_nonneg he hlam.le) hratio hθε
      (Optimization.energy_nonneg (by intro i; positivity)
        (restrictedDensity_nonneg G V P) (fun i j => lt_of_le_of_lt (hcap i j) (by linarith)))
    linarith only [hh,hhad]

end HadwigerRamsey.Main
