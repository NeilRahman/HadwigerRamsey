import HadwigerRamsey4Col.ComponentProgram
import HadwigerRamsey4Col.Sampling
import HadwigerRamsey4Col.Ramsey
import HadwigerRamsey.ThomasonLower

open scoped Classical BigOperators
open Set MeasureTheory ProbabilityTheory Real HadwigerRamsey

namespace HadwigerRamsey4Col.Construction

lemma restricted_colour_model {n m r : ℕ} (p : Edge n → Fin r → ℝ)
    (hp : ∀ e c, 0 ≤ p e c) (hs : ∀ e, ∑ c, p e c = 1)
    (c : Fin r) (f : Fin m → Fin n) (hf : StrictMono f) :
    (∀ e : Edge m, MeasurableSet (edgeEvent (fun ω => (colourGraph c ω).comap f) e)) ∧
    iIndepSet (edgeEvent (fun ω => (colourGraph c ω).comap f)) (labelsMeasure p hp hs) ∧
    ∀ e, (labelsMeasure p hp hs).real (edgeEvent (fun ω => (colourGraph c ω).comap f) e) =
      p (Existence.edgeEmb f hf e) c := by
  have he : edgeEvent (fun ω => (colourGraph c ω).comap f) =
      (fun e : Edge m => {ω | ω (Existence.edgeEmb f hf e) = c}) := by
    funext e
    ext ω
    exact colourGraph_edge c ω (Existence.edgeEmb f hf e)
  rw [he]
  exact ⟨fun e => (measurable_pi_apply _) (measurableSet_singleton _),
    iIndepSet.precomp (Existence.edgeEmb_injective f hf) (labels_independent p hp hs c),
    fun e => label_probability p hp hs _ c⟩

lemma hadwigerNumber_le_one_of_no_edges {n : ℕ} (G : SimpleGraph (Fin n))
    (h : ∀ u v, ¬ G.Adj u v) : hadwigerNumber G ≤ 1 := by
  by_contra hn
  have h2 : 2 ≤ hadwigerNumber G := by omega
  obtain ⟨B,hc,hd,he⟩ := (hadwigerNumber_hasCliqueMinor G).mono h2
  obtain ⟨u,hu,v,hv,huv⟩ := he (0 : Fin 2) 1 (by decide)
  exact h u v huv

lemma edgeOf_density {r n : ℕ} (I : ComponentInstance r) (τ : Fin n → Fin I.k)
    (c : Fin r) (u v : Fin n) (h : u ≠ v) :
    I.density c (τ (Existence.edgeOf u v h).val.1) (τ (Existence.edgeOf u v h).val.2) =
      I.density c (τ u) (τ v) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · simp [Existence.edgeOf, min_eq_left hlt.le, max_eq_right hlt.le]
  · simp only [Existence.edgeOf, min_eq_right hgt.le, max_eq_left hgt.le]
    exact I.density_symm c _ _

/-- The finite probability and component-minor assembly for Theorem 4.
The input bounds are numerical conditions on an actual vertex partition;
all colouring, independence, zero-probability, and component arguments are proved here. -/
theorem finite_construction {r : ℕ} (I : ComponentInstance r) {δ : ℝ}
    (hδ : 0 < δ) (hδprob : (r : ℝ) * I.k * δ < 1)
    (hdensity : ∀ c i j, I.density c i j ≤ 1-δ) :
    ∃ N : ℕ, ∀ (n : ℕ) (τ : Fin n → Fin I.k)
      (m : Fin r → Fin I.k → ℕ)
      (f : ∀ c t, Fin (m c t) → Fin n),
      (∀ c t, StrictMono (f c t)) →
      (∀ c t v, I.label c (τ (f c t v)) = t) →
      (∀ c t v, I.label c (τ v) = t → v ∈ range (f c t)) →
      ∀ R : ℝ, 1 ≤ R →
      (∀ c t, 0 < I.energy c t →
        N ≤ m c t ∧
        δ < sqrt (blockLambda (τ ∘ f c t) (I.density c)) ∧
        (1+δ)*sqrt (blockLambda (τ ∘ f c t) (I.density c)) * (m c t) /
          sqrt (log (m c t : ℝ)) ≤ R) →
      ∃ G : Fin r → SimpleGraph (Fin n), IsDecomposition G ∧
        ∀ c, (hadwigerNumber (G c) : ℝ) ≤ R := by
  classical
  obtain ⟨N,hN⟩ := thomasonlower δ hδ
  refine ⟨N, ?_⟩
  intro n τ m f hf hlabel hcover R hR hb
  let p : Edge n → Fin r → ℝ := fun e c => I.density c (τ e.val.1) (τ e.val.2)
  have hp : ∀ e c, 0 ≤ p e c := fun e c => I.density_nonneg c _ _
  have hs : ∀ e, ∑ c, p e c = 1 := fun e => I.density_sum _ _
  let μ := labelsMeasure p hp hs
  let H := fun c t (ω : Edge n → Fin r) => (colourGraph c ω).comap (f c t)
  have hmodel := fun c t => restricted_colour_model p hp hs c (f c t) (hf c t)
  let A : Fin r × Fin I.k → Set (Edge n → Fin r) := fun a =>
    if 0 < I.energy a.1 a.2 then {ω | (hadwigerNumber (H a.1 a.2 ω) : ℝ) ≤ R}
    else univ
  have hA : ∀ a, MeasurableSet (A a) := by
    intro a
    dsimp only [A]
    split_ifs
    · exact measurableSet_graph_property (H a.1 a.2) (hmodel _ _).1
        (fun G => (hadwigerNumber G : ℝ) ≤ R)
    · exact MeasurableSet.univ
  have hPA : ∀ a, 1-δ ≤ μ.real (A a) := by
    rintro ⟨c,t⟩
    dsimp only [A]
    split_ifs with he
    · obtain ⟨hm, hL, hbound⟩ := hb c t he
      have hprob := hN (m c t) hm I.k (τ ∘ f c t) (I.density c)
        (I.density_symm c) (I.density_nonneg c) (hdensity c) hL μ (H c t)
        (hmodel c t).1 (hmodel c t).2.1 (by
          intro e
          exact (hmodel c t).2.2 e)
      exact hprob.trans (measureReal_mono (fun ω hω => hω.trans hbound))
    · simpa using (show 1-δ ≤ (1 : ℝ) by linarith)
  let Z : Edge n × Fin r → Set (Edge n → Fin r) := fun a =>
    if p a.1 a.2 = 0 then {ω | ω a.1 = a.2} else ∅
  have hZ : ∀ a, MeasurableSet (Z a) := by
    intro a
    dsimp only [Z]
    split_ifs
    · exact (measurable_pi_apply _) (measurableSet_singleton _)
    · exact MeasurableSet.empty
  have hZ0 : ∀ a, μ.real (Z a) = 0 := by
    intro a
    dsimp only [Z]
    split_ifs with h
    · exact (label_probability p hp hs _ _).trans h
    · exact measureReal_empty
  obtain ⟨ω, hω, hz⟩ := exists_all_good μ A hA Z hZ
    (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hδprob) hPA hZ0
  have hadj : ∀ c u v, (colourGraph c ω).Adj u v → I.density c (τ u) (τ v) ≠ 0 := by
    intro c u v ⟨huv, hcol⟩ hzero
    have hz' := hz (Existence.edgeOf u v huv, c)
    apply hz'
    have he : p (Existence.edgeOf u v huv) c = 0 := by
      dsimp only [p]
      rw [edgeOf_density, hzero]
    simpa only [Z, he, if_pos, mem_ofPred_eq] using hcol
  refine ⟨fun c => colourGraph c ω, fun u v huv => colourGraph_partition ω u v huv, ?_⟩
  intro c
  apply hadwigerNumber_le_of_components (colourGraph c ω) (fun v => I.label c (τ v))
    (m c) (f c) (fun t => (hf c t).injective) (hcover c)
  · intro u v huv
    by_contra h
    exact hadj c u v huv (I.density_zero c _ _ h)
  · linarith
  · intro t
    by_cases he : 0 < I.energy c t
    · simpa only [A, he, if_pos, mem_ofPred_eq] using hω (c,t)
    · have hzero : I.energy c t = 0 := le_antisymm (le_of_not_gt he) (sqrt_nonneg _)
      have hbot : ∀ u v, ¬ (H c t ω).Adj u v := by
        intro u v huv
        exact hadj c (f c t u) (f c t v) huv
          (I.density_zero_of_energy_zero c t hzero _ _ (hlabel c t u) (hlabel c t v))
      exact (show (hadwigerNumber (H c t ω) : ℝ) ≤ 1 by
        exact_mod_cast hadwigerNumber_le_one_of_no_edges (H c t ω) hbot).trans hR

end HadwigerRamsey4Col.Construction
