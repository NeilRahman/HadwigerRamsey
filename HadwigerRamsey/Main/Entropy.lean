import HadwigerRamsey.ThomasonUpper
import HadwigerRamsey.ThomasonUpper.Restriction
import HadwigerRamsey.ControlledPartition.Interpretation
import HadwigerRamsey.ControlledPartition.Connectivity
import HadwigerRamsey.Opt
import HadwigerRamsey.Existence.MinorTools

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper HadwigerRamsey.ControlledPartition

namespace HadwigerRamsey.Main

def ThomasonBound (θ : ℝ) (N : ℕ) : Prop :=
  ∀ m ≥ N, ∀ H : SimpleGraph (Fin m),
    θ*m ≤ (vertexConnectivity H : ℝ) →
    ∀ k : ℕ, ∀ σ : Fin m → Fin k, (∀ i, θ ≤ classMass σ i) →
    (m : ℝ)/sqrt (log (m : ℝ))*(sqrt (cappedLambda H σ θ)-θ) ≤
      (hadwigerNumber H : ℝ)

theorem exists_thomason_bound {θ : ℝ} (hθ : 0 < θ) :
    ∃ N : ℕ, ThomasonBound θ N := thomasonupper θ hθ

theorem image_enumeration {n : ℕ} (P : Finset (Fin n)) :
    (univ : Finset (Fin P.card)).image (fun i => (P.equivFin.symm i).val) = P := by
  classical
  ext v
  constructor
  · rintro hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact (P.equivFin.symm i).property
  · intro hv
    exact mem_image.mpr ⟨P.equivFin ⟨v,hv⟩,mem_univ _,by simp⟩

theorem inducedGraph_hadwiger_le {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) : hadwigerNumber (inducedGraph G P) ≤ hadwigerNumber G := by
  apply hadwigerNumber_comap_le
  intro i j hij
  exact P.equivFin.symm.injective (Subtype.ext hij)

theorem internalDensity_inducedGraph {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) : internalDensity (inducedGraph G P) univ = internalDensity G P := by
  have hf : Function.Injective (fun i : Fin P.card => (P.equivFin.symm i).val) := by
    intro i j hij
    exact P.equivFin.symm.injective (Subtype.ext hij)
  exact (internalDensity_comap G _ hf univ).trans
    (congrArg (internalDensity G) (image_enumeration P))

/-- The one-class application in condition (c) of the main proof. -/
theorem singleton_entropy_lower {n N : ℕ} (G : SimpleGraph (Fin n))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hthom : ThomasonBound θ N)
    (P : Finset (Fin n)) (hP : P.Nonempty) (hN : N ≤ P.card)
    (hconn : RealConnected G P (θ*P.card))
    (hcap : internalDensity G P ≤ 1-θ) :
    (P.card : ℝ)/sqrt (log (P.card : ℝ)) *
      (sqrt (-log (1-internalDensity G P))-θ) ≤ (hadwigerNumber G : ℝ) := by
  classical
  let H := inducedGraph G P
  let σ : Fin P.card → Fin 1 := fun _ => 0
  have hmass : ∀ i, θ ≤ classMass σ i := by
    intro i
    have hm : classMass σ i = 1 := by
      unfold classMass
      have hi : i = 0 := Subsingleton.elim _ _
      simp only [σ,hi,univ.filter_true,card_univ,Fintype.card_fin]
      exact div_self (by exact_mod_cast hP.card_pos.ne')
    rw [hm]
    exact hθ1
  have hκ := (realConnected_iff_vertexConnectivity G P hP _).mp hconn
  have hh := hthom P.card hN H hκ 1 σ hmass
  have hverts : classVertices σ 0 = univ := by ext v; simp [classVertices,σ]
  have hq : cappedDensity H σ θ 0 0 = internalDensity G P := by
    simp [cappedDensity,blockDensity,hverts,H,
      internalDensity_inducedGraph,min_eq_left hcap]
  have hΛ : cappedLambda H σ θ = -log (1-internalDensity G P) := by
    have hm : classMass σ 0 = 1 := by
      unfold classMass
      simp only [σ,univ.filter_true,card_univ,Fintype.card_fin]
      exact div_self (by exact_mod_cast hP.card_pos.ne')
    simp only [cappedLambda,blockLambda,Fin.sum_univ_one,hm,hq,one_mul]
  rw [hΛ] at hh
  exact hh.trans (by exact_mod_cast inducedGraph_hadwiger_le G P)

theorem sum_injective_le {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (F : J → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∑ i, F (f i) ≤ ∑ j, F j := by
  classical
  calc
    _ = ∑ j ∈ univ.image f, F j := (sum_image (by intro i _ j _ h; exact hf h)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intro j _ _; exact hF j)

end HadwigerRamsey.Main

namespace HadwigerRamsey.Main

/-- A selected submatrix contributes no more than the whole nonnegative entropy. -/
theorem active_energy_le {d k m : ℕ} (H : SimpleGraph (Fin d))
    (σ : Fin d → Fin k) {θ w : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hw : 0 ≤ w) (f : Fin m → Fin k) (hf : Function.Injective f)
    (α : Fin m → ℝ) (q : Fin m → Fin m → ℝ)
    (hα : ∀ i, 0 ≤ α i)
    (hmass : ∀ i, w*α i ≤ classMass σ (f i))
    (hq : ∀ i j, q i j = blockDensity H σ (f i) (f j))
    (hcap : ∀ i j, q i j ≤ 1-θ) :
    w^2 * Optimization.energy α q ≤ cappedLambda H σ θ := by
  have hq0 : ∀ i j, 0 ≤ q i j := by
    intro i j
    rw [hq]
    exact blockDensity_nonneg _ _ _ _
  have hq1 : ∀ i j, q i j < 1 := by intro i j; linarith [hcap i j]
  have hqcap : ∀ i j, cappedDensity H σ θ (f i) (f j) = q i j := by
    intro i j
    rw [cappedDensity,←hq]
    exact min_eq_left (hcap i j)
  let F := fun i j => classMass σ i * classMass σ j *
    (-log (1-cappedDensity H σ θ i j))
  have hF : ∀ i j, 0 ≤ F i j := by
    intro i j
    apply mul_nonneg (mul_nonneg (classMass_nonneg _ _) (classMass_nonneg _ _))
    exact (log_weight_bounds hθ (cappedDensity_bounds H σ hθ1 i j).1
      (cappedDensity_bounds H σ hθ1 i j).2).1
  have hterm : ∀ i j, w^2*(α i*α j*Optimization.logCost (q i j)) ≤ F (f i) (f j) := by
    intro i j
    have hh := mul_le_mul (hmass i) (hmass j) (mul_nonneg hw (hα j))
      (classMass_nonneg σ (f i))
    have hlog := Optimization.logCost_nonneg (hq0 i j) (hq1 i j)
    have hh' := mul_le_mul_of_nonneg_right hh hlog
    dsimp [F]
    rw [hqcap]
    dsimp [Optimization.logCost] at *
    nlinarith only [hh']
  have hfirst : w^2*Optimization.energy α q ≤ ∑ i, ∑ j, F (f i) (f j) := by
    unfold Optimization.energy
    simp only [mul_sum]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
  have hsecond : (∑ i, ∑ j, F (f i) (f j)) ≤ ∑ i, ∑ j, F i j := by
    calc
      _ ≤ ∑ i, ∑ j, F (f i) j := sum_le_sum fun i _ =>
        sum_injective_le f hf (F (f i)) (hF (f i))
      _ ≤ _ := sum_injective_le f hf (fun i => ∑ j, F i j)
        (fun i => sum_nonneg fun j _ => hF i j)
  exact hfirst.trans hsecond

/-- The multitype application of Theorem 1.5 on an induced set, normalized by
an ambient order n. Active partition classes may omit other classes. -/
theorem induced_entropy_upper {n N k m : ℕ} (G : SimpleGraph (Fin n))
    {θ c : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hc : 0 ≤ c)
    (hthom : ThomasonBound θ N) (P : Finset (Fin n)) (hP2 : 2 ≤ P.card)
    (hN : N ≤ P.card) (hconn : RealConnected G P (θ*P.card))
    (σ : Fin P.card → Fin k) (hmassall : ∀ j, θ ≤ classMass σ j)
    (f : Fin m → Fin k) (hf : Function.Injective f)
    (α : Fin m → ℝ) (q : Fin m → Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hmass : ∀ i, c*(n : ℝ)/P.card*α i ≤ classMass σ (f i))
    (hq : ∀ i j, q i j = blockDensity (inducedGraph G P) σ (f i) (f j))
    (hcap : ∀ i j, q i j ≤ 1-θ) :
    c*sqrt (Optimization.energy α q) ≤
      (hadwigerNumber G : ℝ)*sqrt (log (n : ℝ))/(n : ℝ)+θ := by
  have hPn : P.card ≤ n := by simpa using P.card_le_univ
  have hPR : (0 : ℝ) < P.card := by exact_mod_cast (by omega : 0 < P.card)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hPnon : P.Nonempty := card_pos.mp (by omega)
  let H := inducedGraph G P
  have hκ := (realConnected_iff_vertexConnectivity G P hPnon _).mp hconn
  have ht := hthom P.card hN H hκ k σ hmassall
  have hE := active_energy_le H σ hθ hθ1 (by positivity : 0 ≤ c*(n : ℝ)/P.card)
    f hf α q hα hmass hq hcap
  have hq0 : ∀ i j, 0 ≤ q i j := by
    intro i j
    rw [hq]
    exact blockDensity_nonneg _ _ _ _
  have hq1 : ∀ i j, q i j < 1 := by intro i j; linarith [hcap i j]
  have hEnon := Optimization.energy_nonneg hα hq0 hq1
  have hΛnon := cappedLambda_nonneg H σ hθ hθ1
  have hroot : c*(n : ℝ)/P.card*sqrt (Optimization.energy α q) ≤ sqrt (cappedLambda H σ θ) := by
    have hh := sqrt_le_sqrt hE
    rw [sqrt_mul (sq_nonneg _),sqrt_sq_eq_abs,abs_of_nonneg (show 0 ≤ c*(n : ℝ)/P.card by positivity)] at hh
    exact hh
  have hrootP : 0 < sqrt (log (P.card : ℝ)) :=
    sqrt_pos.mpr (log_pos (by exact_mod_cast (by omega : 1 < P.card)))
  have hroots : sqrt (log (P.card : ℝ)) ≤ sqrt (log (n : ℝ)) :=
    sqrt_le_sqrt (log_le_log hPR (by exact_mod_cast hPn))
  have hHG : (hadwigerNumber H : ℝ) ≤ hadwigerNumber G := by
    exact_mod_cast inducedGraph_hadwiger_le G P
  have ht' : sqrt (cappedLambda H σ θ)-θ ≤
      (hadwigerNumber G : ℝ)*sqrt (log (P.card : ℝ))/P.card := by
    have hh := ht.trans hHG
    have hpos : 0 < (P.card : ℝ)/sqrt (log (P.card : ℝ)) := div_pos hPR hrootP
    have hh' : (sqrt (cappedLambda H σ θ)-θ)*((P.card : ℝ)/sqrt (log (P.card : ℝ))) ≤ (hadwigerNumber G : ℝ) := by nlinarith only [hh]
    have hd := (le_div_iff₀ hpos).mpr hh'
    convert hd using 1 <;> first | rfl | field_simp
  have hbound : c*(n : ℝ)/P.card*sqrt (Optimization.energy α q) ≤ (hadwigerNumber G : ℝ)*sqrt (log (P.card : ℝ))/P.card+θ := by linarith only [hroot,ht']
  have hmult := mul_le_mul_of_nonneg_right hbound hPR.le
  have he : (c*(n : ℝ)/P.card*sqrt (Optimization.energy α q))*(P.card : ℝ) =
      c*(n : ℝ)*sqrt (Optimization.energy α q) := by field_simp
  have he' : (((hadwigerNumber G : ℝ)*sqrt (log (P.card : ℝ))/P.card)+θ)*(P.card : ℝ) =
      (hadwigerNumber G : ℝ)*sqrt (log (P.card : ℝ))+θ*P.card := by field_simp
  rw [he,he'] at hmult
  have hhP := mul_le_mul_of_nonneg_left (show (P.card : ℝ) ≤ n by exact_mod_cast hPn) hθ.le
  have hhroot := mul_le_mul_of_nonneg_left hroots (show (0 : ℝ) ≤ hadwigerNumber G by positivity)
  have hd := div_mul_cancel₀ ((hadwigerNumber G : ℝ)*sqrt (log (n : ℝ))) hnR.ne'
  by_contra! hbad
  have hbad' := mul_lt_mul_of_pos_right hbad hnR
  nlinarith only [hmult,hhP,hhroot,hd,hbad']

end HadwigerRamsey.Main

namespace HadwigerRamsey.Main

/-- Normalize an induced-graph lower bound to the ambient graph order. -/
theorem normalize_lower {n r : ℕ} {X θ H : ℝ} (hr2 : 2 ≤ r) (hrn : r ≤ n)
    (hθ : 0 ≤ θ) (hH : 0 ≤ H)
    (hbound : (r : ℝ)/sqrt (log (r : ℝ))*(X-θ) ≤ H) :
    (r : ℝ)/(n : ℝ)*X ≤ H*sqrt (log (n : ℝ))/(n : ℝ)+θ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hroot : 0 < sqrt (log (r : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast (by omega : 1 < r)))
  have hh : (r : ℝ)*(X-θ) ≤ H*sqrt (log (r : ℝ)) := by
    apply (div_le_iff₀ hroot).mp
    simpa only [div_mul_eq_mul_div] using hbound
  have hroots := sqrt_le_sqrt (log_le_log hrR (show (r : ℝ) ≤ n by exact_mod_cast hrn))
  have hHroots := mul_le_mul_of_nonneg_left hroots hH
  have hθr := mul_le_mul_of_nonneg_left (show (r : ℝ) ≤ n by exact_mod_cast hrn) hθ
  have he : ((r : ℝ)/(n : ℝ)*X)*(n : ℝ) = r*X := by field_simp
  have he' := div_mul_cancel₀ (H*sqrt (log (n : ℝ))) hnR.ne'
  by_contra! hbad
  have hbad' := mul_lt_mul_of_pos_right hbad hnR
  rw [he] at hbad'
  nlinarith only [hh,hHroots,hθr,he',hbad']

/-- Condition (c), as an upper bound on the normalized singleton entropy. -/
theorem singleton_entropy_upper {n N : ℕ} (G : SimpleGraph (Fin n))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hthom : ThomasonBound θ N)
    (P : Finset (Fin n)) (hP2 : 2 ≤ P.card) (hN : N ≤ P.card)
    (hconn : RealConnected G P (θ*P.card))
    (hcap : internalDensity G P ≤ 1-θ) :
    (P.card : ℝ)/(n : ℝ)*sqrt (-log (1-internalDensity G P)) ≤
      (hadwigerNumber G : ℝ)*sqrt (log (n : ℝ))/(n : ℝ)+θ := by
  exact normalize_lower hP2 (by simpa using P.card_le_univ) hθ.le (by positivity)
    (singleton_entropy_lower G hθ hθ1 hthom P (card_pos.mp (by omega)) hN hconn hcap)

end HadwigerRamsey.Main
