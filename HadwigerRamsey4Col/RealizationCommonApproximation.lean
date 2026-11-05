import HadwigerRamsey4Col.RealizationConvergenceCost
import Graphon.FiniteFactorApproximation
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators Classical Topology
open MeasureTheory Set Filter

namespace HadwigerRamsey4Col.Realization

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- A shared finite marking for every colour, refining a prescribed marking. -/
structure CommonFiniteApproximation {r k : ℕ} (W : Fin r → Graphon α μ)
    (original : α → Fin k) (ε : ℝ) where
  n : ℕ
  mark : α → Fin n
  measurable_mark : Measurable mark
  label : Fin n → Fin k
  refines : ∀ x, label (mark x) = original x
  matrix : Fin r → Fin n → Fin n → ℝ
  matrix_symm : ∀ c i j, matrix c i j = matrix c j i
  matrix_bounds : ∀ c i j, matrix c i j ∈ Icc (0 : ℝ) 1
  error_le : ∀ c, Graphon.cutNormDiff (W c)
    (markedGraphon (matrix c) (matrix_symm c) (matrix_bounds c) mark measurable_mark) ≤ ε

namespace CommonFiniteApproximation

variable {r k : ℕ} {W : Fin r → Graphon α μ} {original : α → Fin k} {ε : ℝ}

noncomputable def graphon (P : CommonFiniteApproximation W original ε) (c : Fin r) :
    Graphon α μ :=
  markedGraphon (P.matrix c) (P.matrix_symm c) (P.matrix_bounds c) P.mark P.measurable_mark

theorem graphon_error_le (P : CommonFiniteApproximation W original ε) (c : Fin r) :
    Graphon.cutNormDiff (W c) (P.graphon c) ≤ ε := P.error_le c

end CommonFiniteApproximation

/-- Finitely many graphons have simultaneous finite approximations on one
marking which remembers every original partition class. -/
theorem exists_commonFiniteApproximation {r k : ℕ} (W : Fin r → Graphon α μ)
    (original : α → Fin k) (horiginal : Measurable original) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (CommonFiniteApproximation W original ε) := by
  have hp : ∀ c : Fin r, ∃ P : MeasurablePartition α μ,
      Graphon.cutNormDiff (W c) (Graphon.stepify P (W c)) ≤ ε := by
    intro c
    obtain ⟨P, _, hP⟩ := Graphon.regularity (W c) ε hε
    exact ⟨P, hP⟩
  choose P hP using hp
  let K := Fin k × (∀ c : Fin r, Fin ((P c).parts.card + 1))
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let mark : α → Fin (Fintype.card K) := fun x =>
    e (original x, fun c => Graphon.partIndex (P c) x)
  have hmark : Measurable mark := by
    apply (Measurable.of_discrete : Measurable e).comp
    exact horiginal.prodMk (measurable_pi_iff.mpr fun c => Graphon.measurable_partIndex (P c))
  let B : Fin r → Fin (Fintype.card K) → Fin (Fintype.card K) → ℝ := fun c i j =>
    Graphon.stepMatrix (P c) (W c) ((e.symm i).2 c) ((e.symm j).2 c)
  have hBsymm : ∀ c i j, B c i j = B c j i :=
    fun c i j => Graphon.stepMatrix_symm (P c) (W c) _ _
  have hB : ∀ c i j, B c i j ∈ Icc (0 : ℝ) 1 :=
    fun c i j => Graphon.stepMatrix_mem_Icc (P c) (W c) _ _
  have hEq (c : Fin r) :
      markedGraphon (μ := μ) (B c) (hBsymm c) (hB c) mark hmark =
        Graphon.stepify (P c) (W c) := by
    rw [← Graphon.pullback_stepKernel (P c) (W c)]
    apply Graphon.ext
    apply SymmKernel.ext
    apply AEEqFun.ext
    have hker : ∀ᵐ p ∂μ.prod μ,
        (Graphon.stepKernel (P c) (W c)).toAEEqFun
          (Graphon.partIndex (P c) p.1, Graphon.partIndex (P c) p.2) =
        Graphon.stepMatrix (P c) (W c) (Graphon.partIndex (P c) p.1)
          (Graphon.partIndex (P c) p.2) :=
      ((Graphon.measurePreserving_partIndex (P c)).prod
        (Graphon.measurePreserving_partIndex (P c))).quasiMeasurePreserving.ae
          (Graphon.stepKernel_ae (P c) (W c))
    filter_upwards [markedGraphon_ae (B c) (hBsymm c) (hB c) mark hmark,
      Graphon.pullback_ae (Graphon.stepKernel (P c) (W c)) (Graphon.partIndex (P c))
        (Graphon.measurePreserving_partIndex (P c)), hker] with p hm hp hk
    rw [hm, hp, hk]
    simp [B, mark]
  refine ⟨{ n := Fintype.card K
            mark := mark
            measurable_mark := hmark
            label := fun i => (e.symm i).1
            refines := ?_
            matrix := B
            matrix_symm := hBsymm
            matrix_bounds := hB
            error_le := ?_ }⟩
  · intro x
    simp [mark]
  · intro c
    rw [hEq]
    exact hP c

/-- Fixed countable approximations, suitable for simultaneous realization of all
finite marked tests. -/
noncomputable def commonFiniteApproximationSequence {r k : ℕ}
    (W : Fin r → Graphon α μ) (original : α → Fin k) (horiginal : Measurable original)
    (l : ℕ) : CommonFiniteApproximation W original (1 / ((l : ℝ) + 1)) :=
  Classical.choice (exists_commonFiniteApproximation W original horiginal (by positivity))

theorem commonFiniteApproximationSequence_tendsto {r k : ℕ}
    (W : Fin r → Graphon α μ) (original : α → Fin k) (horiginal : Measurable original)
    (c : Fin r) :
    Tendsto (fun l => Graphon.cutNormDiff (W c)
      ((commonFiniteApproximationSequence W original horiginal l).graphon c))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun l => Graphon.cutNormDiff_nonneg _ _)
    (fun l => (commonFiniteApproximationSequence W original horiginal l).graphon_error_le c)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end HadwigerRamsey4Col.Realization
