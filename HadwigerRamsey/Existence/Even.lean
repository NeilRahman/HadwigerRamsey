import HadwigerRamsey.ThomasonLower
import HadwigerRamsey.Existence.Blocks
import HadwigerRamsey.Existence.MinorTools
import HadwigerRamsey.Existence.Scale
import HadwigerRamsey.Existence.Outcome

open scoped BigOperators Classical Topology
open Finset Set Real MeasureTheory ProbabilityTheory Filter
namespace HadwigerRamsey.Existence
set_option maxHeartbeats 1200000

/-- The even-order construction, before reindexing the three labels. -/
theorem even_construction (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℕ, ∀ m ≥ M, ∃ ω : Edge (2*m) → Label,
      ∀ a : Label, (hadwigerNumber (colourGraph a ω) : ℝ) ≤
        (1+eta)*beta*(2*m)/sqrt (log (2*(m : ℝ))) := by
  have hp0 := p_bounds.1
  have hb0 := beta_positive
  let d := min (eta/4) (min (p/4) (min (beta/4) (1/16)))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hde : d ≤ eta/4 := min_le_left _ _
  have hdp : d ≤ p/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdb : d ≤ beta/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd16 : d ≤ 1/16 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N,hN⟩ := thomasonlower d hd
  obtain ⟨S,hS⟩ := eventually_atTop.mp (eventually_half_scale heta hd.le (by linarith only [hde,heta]))
  refine ⟨max (max N S) 2,?_⟩
  intro m hm
  have hmN : N ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmS : S ≤ m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  obtain ⟨_,hroot,hscale⟩ := hS m hmS
  have hmR2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hroot2 : 0 < sqrt (log (2*(m : ℝ))) := sqrt_pos.mpr (log_pos (by nlinarith only [hmR2]))
  let μ := labelsMeasure (rate m) (rate_nonneg m) (rate_half m)
  let H := fun (i : Fin 2) (ω : Edge (2*m) → Label) => (colourGraph none ω).comap (halfMap m i)
  let Q := fun (a : Label) (ω : Edge (2*m) → Label) => (colourGraph a ω).comap (id : Fin (2*m) → Fin (2*m))
  have hHmodel := fun i => colour_model (rate m) (rate_nonneg m) (rate_half m) none (halfMap m i) (halfMap_strict m i)
  have hQmodel := fun a => colour_model (rate m) (rate_nonneg m) (rate_half m) a id (strictMono_id)
  have hsingle : blockLambda (fun _ : Fin m => (0 : Fin 1)) (fun _ _ => 1-2*p) = -log (2*p) := by
    simp [blockLambda,classMass,hmpos.ne',show (m : ℝ) ≠ 0 by exact_mod_cast hmpos.ne']
  have hPhalf : ∀ i, 1-d ≤ μ.real {ω | (hadwigerNumber (H i ω) : ℝ) ≤ (1+d)*(2*beta)*m/sqrt (log (m : ℝ))} := by
    intro i
    have hh := hN m hmN 1 (fun _ => 0) (fun _ _ => 1-2*p)
      (fun _ _ => rfl) (fun _ _ => by linarith [p_bounds.2])
      (fun _ _ => by linarith only [hdp,p_bounds.1])
      (by rw [hsingle,sqrt_internal]; linarith only [hdb,beta_positive]) μ (H i)
      (hHmodel i).1 (hHmodel i).2.1 (by
        intro e
        rw [(hHmodel i).2.2 e]
        simp [rate,edgeEmb,halfClass_map])
    simpa only [hsingle,sqrt_internal] using hh
  have hPfull : ∀ b : Bool, 1-d ≤ μ.real {ω | (hadwigerNumber (Q (some b) ω) : ℝ) ≤ (1+d)*beta*(2*m)/sqrt (log (2*(m : ℝ)))} := by
    intro b
    have hh := hN (2*m) (by omega) 2 halfClass mixed mixed_symmetric mixed_nonneg
      (by intro i j; unfold mixed; split_ifs <;> linarith [p_bounds.2])
      (by rw [mixed_entropy hmpos,sqrt_sq beta_positive.le]; linarith only [hdb,beta_positive]) μ (Q (some b))
      (hQmodel (some b)).1 (hQmodel (some b)).2.1 (by
        intro e
        rw [(hQmodel (some b)).2.2 e]
        rfl)
    simpa only [mixed_entropy hmpos,sqrt_sq beta_positive.le,Nat.cast_mul,Nat.cast_ofNat] using hh
  let R := (1+eta)*beta*(2*m)/sqrt (log (2*(m : ℝ)))
  have hhalfR : (1+d)*(2*beta)*m/sqrt (log (m : ℝ)) ≤ R := by
    apply (div_le_div_iff₀ hroot hroot2).mpr
    have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg beta_positive.le hmR.le)
    nlinarith only [hh]
  have hfullR : (1+d)*beta*(2*m)/sqrt (log (2*(m : ℝ))) ≤ R := by
    dsimp only [R]
    gcongr
    linarith only [hde,heta]
  let A : Fin 4 → Set (Edge (2*m) → Label) :=
    ![{ω | (hadwigerNumber (H 0 ω) : ℝ) ≤ R}, {ω | (hadwigerNumber (H 1 ω) : ℝ) ≤ R},
      {ω | (hadwigerNumber (Q (some true) ω) : ℝ) ≤ R}, {ω | (hadwigerNumber (Q (some false) ω) : ℝ) ≤ R}]
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i; fin_cases i
    · exact measurableSet_graph_property (H 0) (hHmodel 0).1 (fun G => (hadwigerNumber G : ℝ) ≤ R)
    · exact measurableSet_graph_property (H 1) (hHmodel 1).1 (fun G => (hadwigerNumber G : ℝ) ≤ R)
    · exact measurableSet_graph_property (Q (some true)) (hQmodel _).1 (fun G => (hadwigerNumber G : ℝ) ≤ R)
    · exact measurableSet_graph_property (Q (some false)) (hQmodel _).1 (fun G => (hadwigerNumber G : ℝ) ≤ R)
  have hPA : ∀ i, 1-d ≤ μ.real (A i) := by
    intro i; fin_cases i
    · exact (hPhalf 0).trans (measureReal_mono (fun ω h => h.trans hhalfR))
    · exact (hPhalf 1).trans (measureReal_mono (fun ω h => h.trans hhalfR))
    · exact (hPfull true).trans (measureReal_mono (fun ω h => h.trans hfullR))
    · exact (hPfull false).trans (measureReal_mono (fun ω h => h.trans hfullR))
  let Z := fun e : Edge (2*m) => if halfClass e.val.1 = halfClass e.val.2 then ∅ else {ω : Edge (2*m) → Label | ω e = none}
  have hZ : ∀ e, MeasurableSet (Z e) := by
    intro e; dsimp only [Z]; split_ifs
    · exact MeasurableSet.empty
    · exact (measurable_pi_apply e) (measurableSet_singleton _)
  have hZ0 : ∀ e, μ.real (Z e) = 0 := by
    intro e; dsimp only [Z]; split_ifs with he
    · exact measureReal_empty
    · rw [label_probability]
      simp [rate,he]
  obtain ⟨ω,hω,hcross⟩ := exists_four_good μ A hA Z hZ (by linarith only [hd16] : 4*d < 1) hPA hZ0
  refine ⟨ω,?_⟩
  intro a
  cases a with
  | none =>
    refine hadwigerNumber_le_of_fibers (colourGraph none ω) halfClass (halfMap m)
      (fun i => (halfMap_strict m i).injective) (halfMap_cover m) ?_ (by positivity) ?_
    · intro u v ⟨huv,ha⟩
      have he := hcross (edgeOf u v huv)
      have hc : halfClass (edgeOf u v huv).val.1 = halfClass (edgeOf u v huv).val.2 := by
        by_contra hc
        exact he (by simpa [Z,hc] using ha)
      rcases lt_or_gt_of_ne huv with hlt | hgt
      · simpa [edgeOf,min_eq_left hlt.le,max_eq_right hlt.le] using hc
      · have hh : halfClass v = halfClass u := by simpa [edgeOf,min_eq_right hgt.le,max_eq_left hgt.le] using hc
        exact hh.symm
    · intro i; fin_cases i
      · simpa [A,H] using hω 0
      · simpa [A,H] using hω 1
  | some b =>
    cases b
    · simpa [A,Q] using hω 3
    · simpa [A,Q] using hω 2
end HadwigerRamsey.Existence
