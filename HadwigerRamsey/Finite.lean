import HadwigerRamsey.Graph
import HadwigerRamsey.Probability
import HadwigerRamsey.Analytic
import HadwigerRamsey.Weights

open scoped BigOperators
open Finset Set MeasureTheory ProbabilityTheory Real
namespace HadwigerRamsey

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} (G : Ω → SimpleGraph (Fin n))

/-- The event that an increasing potential edge is present. -/
def edgeEvent (e : Edge n) : Set Ω := {ω | (G ω).Adj e.val.1 e.val.2}

/-- The logarithmic weights can vary edge by edge; they need not come from blocks. -/
theorem fixed_partition_bound {s : ℕ} (hs : 2 ≤ s) (f : Fin n → Fin s)
    (w : Edge n → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hA : ∀ e, MeasurableSet (edgeEvent G e))
    (hind : iIndepSet (edgeEvent G) μ)
    (hp : ∀ e, μ.real (edgeEvent G e)ᶜ = exp (-w e))
    {T : ℝ} (hT : ∑ e, w e ≤ T) :
    μ.real {ω | Permissible (G ω) f} ≤
      exp (-(Fintype.card (Edge s) : ℝ) * exp (-T / Fintype.card (Edge s))) := by
  classical
  let S : Edge s → Finset (Edge n) := fun a => univ.filter (Crosses f a)
  let W : Edge s → ℝ := fun a => ∑ e ∈ S a, w e
  have hS : _root_.Pairwise (fun a b => Disjoint (S a) (S b)) := by
    intro a b hab
    exact Finset.disjoint_left.mpr (fun e he he' =>
      Set.disjoint_left.mp (crosses_disjoint f hab) (mem_filter.mp he).2 (mem_filter.mp he').2)
  have hhit : ∀ a, μ.real (Hit (edgeEvent G) (S a)) = 1 - exp (-W a) := by
    intro a
    have hno := probability_noHit hA hind (S a)
    have hcompl : ∀ e, 1 - μ.real (edgeEvent G e) = exp (-w e) := by
      intro e
      have := measureReal_add_measureReal_compl (μ := μ) (hA e)
      simp only [probReal_univ] at this
      linarith [hp e]
    simp_rw [hcompl] at hno
    rw [← Real.exp_sum, Finset.sum_neg_distrib] at hno
    have hc := measureReal_add_measureReal_compl (μ := μ) (measurableSet_hit hA (S a))
    simp only [probReal_univ] at hc
    dsimp [W]
    linarith
  have heq : {ω | Permissible (G ω) f} = ⋂ a, Hit (edgeEvent G) (S a) := by
    ext ω
    simp only [Set.mem_setOf_eq, permissible_iff_crosses, Set.mem_iInter, Hit,
      Set.mem_iUnion, S, mem_filter, edgeEvent]
    constructor
    · intro h a
      obtain ⟨e, he, hg⟩ := h a
      exact ⟨e, ⟨mem_univ _, he⟩, hg⟩
    · intro h a
      obtain ⟨e, he, hg⟩ := h a
      exact ⟨e, he.2, hg⟩
  rw [heq]
  have hprod := probability_allHits hA hind S hS univ
  simp only [Finset.mem_univ, Set.iInter_true] at hprod
  rw [hprod]
  simp_rw [hhit]
  have hne : (univ : Finset (Edge s)).Nonempty := by
    exact ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩, mem_univ _⟩
  apply permissible_product_bound univ W hne
    (fun a _ => Finset.sum_nonneg (fun e _ => hw e))
    ((sum_cross_weights_le f w hw).trans hT)

/-- Corollary `cor:finite`: a union bound over all vertex-to-part maps. -/
theorem finite_minor_bound {s : ℕ} (hs : 2 ≤ s)
    (w : Edge n → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hA : ∀ e, MeasurableSet (edgeEvent G e))
    (hind : iIndepSet (edgeEvent G) μ)
    (hp : ∀ e, μ.real (edgeEvent G e)ᶜ = exp (-w e))
    {T : ℝ} (hT : ∑ e, w e ≤ T) :
    μ.real {ω | HasCliqueMinor (G ω) s} ≤ (s : ℝ)^n *
      exp (-(Fintype.card (Edge s) : ℝ) * exp (-T / Fintype.card (Edge s))) := by
  classical
  have hsub : {ω | HasCliqueMinor (G ω) s} ⊆
      ⋃ f : Fin n → Fin s, {ω | Permissible (G ω) f} := by
    intro ω hω
    obtain ⟨f, hf⟩ := hω.permissible (by omega)
    exact Set.mem_iUnion.mpr ⟨f,hf⟩
  calc
    _ ≤ μ.real (⋃ f : Fin n → Fin s, {ω | Permissible (G ω) f}) := measureReal_mono hsub
    _ ≤ ∑ f : Fin n → Fin s, μ.real {ω | Permissible (G ω) f} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _f : Fin n → Fin s,
        exp (-(Fintype.card (Edge s) : ℝ) * exp (-T / Fintype.card (Edge s))) :=
      Finset.sum_le_sum (fun f _ => fixed_partition_bound G hs f w hw hA hind hp hT)
    _ = _ := by simp

end HadwigerRamsey
