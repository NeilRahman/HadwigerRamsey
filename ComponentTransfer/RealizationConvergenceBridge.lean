import ComponentTransfer.RealizationConvergenceCost
import ComponentTransfer.RealizationConvergenceFinite
import ComponentTransfer.RealizationTransportMeasure

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace ComponentTransfer.Realization

/-- A probability coupling, with both marginal maps recorded explicitly. -/
structure ProbabilityCoupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) where
  law : Measure (α × β)
  probability : IsProbabilityMeasure law
  fst_mp : MeasurePreserving Prod.fst law μ
  snd_mp : MeasurePreserving Prod.snd law ν

attribute [instance] ProbabilityCoupling.probability

namespace ProbabilityCoupling

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The cut cost of two kernels under this particular common coupling. -/
noncomputable def cost (π : ProbabilityCoupling μ ν) (U : Graphon α μ) (W : Graphon β ν) : ℝ :=
  Graphon.cutNormDiff (Graphon.pullback U Prod.fst π.fst_mp)
    (Graphon.pullback W Prod.snd π.snd_mp)

lemma cost_nonneg (π : ProbabilityCoupling μ ν) (U : Graphon α μ) (W : Graphon β ν) :
    0 ≤ π.cost U W := Graphon.cutNormDiff_nonneg _ _

end ProbabilityCoupling

/-- Common-coloured cut convergence: for each tolerance one probability
coupling eventually makes every colour's cut error small. The same coupling
must work for all colours. Carriers may vary along the sequence. -/
def CommonCutConverges {r : ℕ} {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : ∀ n, Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (U : ∀ n, Fin r → Graphon (V n) (ν n)) (W : Fin r → Graphon α μ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∃ π : ProbabilityCoupling (ν n) μ,
    ∀ c, π.cost (U n c) (W c) < ε

/-- Common cut convergence for finite matrices. Nonemptiness is required only
eventually, so empty induced graphs at initial indices need no replacement. -/
def FiniteCommonCutConverges {r : ℕ} {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : ∀ n, Fin r → V n → V n → ℝ)
    (hAsymm : ∀ n c i j, A n c i j = A n c j i)
    (hA : ∀ n c i j, A n c i j ∈ Icc (0 : ℝ) 1)
    (W : Fin r → Graphon α μ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∃ hn : Nonempty (V n),
    letI := hn
    ∃ π : ProbabilityCoupling (uniformFiniteMeasure (V n)) μ,
      ∀ c, π.cost (markedGraphon (A n c) (hAsymm n c) (hA n c) id measurable_id) (W c) < ε

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {K : Type*} [Fintype K] [DecidableEq K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

/-- Approximate both tuples by matrices on matching finite markings. A single
coupling then controls every colour simultaneously. -/
theorem exists_common_coupling_of_step_approximation {r : ℕ}
    (U : Fin r → Graphon α μ) (W : Fin r → Graphon β ν)
    (B : Fin r → K → K → ℝ)
    (hBsymm : ∀ c i j, B c i j = B c j i)
    (hB : ∀ c i j, B c i j ∈ Icc (0 : ℝ) 1)
    (left : α → K) (right : β → K) (hleft : Measurable left) (hright : Measurable right)
    {a b d : ℝ}
    (hU : ∀ c, Graphon.cutNormDiff (U c)
      (markedGraphon (B c) (hBsymm c) (hB c) left hleft) ≤ a)
    (hW : ∀ c, Graphon.cutNormDiff (W c)
      (markedGraphon (B c) (hBsymm c) (hB c) right hright) ≤ b)
    (hmass : (∑ i, |μ.real (left ⁻¹' {i}) - ν.real (right ⁻¹' {i})|) ≤ d) :
    ∃ π : ProbabilityCoupling μ ν, ∀ c, π.cost (U c) (W c) ≤ a + b + 2 * d := by
  obtain ⟨π, hπ, hfst, hsnd, hbad⟩ := exists_mark_coupling μ ν left hleft right hright
  let C : ProbabilityCoupling μ ν := ⟨π, hπ, hfst, hsnd⟩
  refine ⟨C, fun c => ?_⟩
  let : IsProbabilityMeasure π := hπ
  have hcost := coupling_cost_le (μ := π) (U c) (W c) (B c) (hBsymm c) (hB c)
    left right hleft hright Prod.fst Prod.snd hfst hsnd
  change Graphon.cutNormDiff (Graphon.pullback (U c) Prod.fst hfst)
    (Graphon.pullback (W c) Prod.snd hsnd) ≤ _
  linarith [hU c, hW c]

section Convergence

variable {r : ℕ} {V : ℕ → Type*}
  [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
  [∀ n, MeasurableSingletonClass (V n)]

/-- A finite marked approximation sequence, convergence of its masses, and
convergence of its residual four-cycle tests imply common-coloured cut
convergence. The coupling is shared by every colour. -/
theorem finiteCommonCutConverges_of_C4
    (A : ∀ n, Fin r → V n → V n → ℝ)
    (hAsymm : ∀ n c i j, A n c i j = A n c j i)
    (hA : ∀ n c i j, A n c i j ∈ Icc (0 : ℝ) 1)
    (W : Fin r → Graphon α μ)
    (k : ℕ → ℕ) (marks : ∀ l, α → Fin (k l))
    (hmeas : ∀ l, Measurable (marks l))
    (B : ∀ l, Fin r → Fin (k l) → Fin (k l) → ℝ)
    (hsymm : ∀ l c i j, B l c i j = B l c j i)
    (hbounds : ∀ l c i j, B l c i j ∈ Icc (0 : ℝ) 1)
    (labels : ∀ l n, V n → Fin (k l))
    (hnonempty : ∀ᶠ n in atTop, Nonempty (V n))
    (happrox : ∀ c, Tendsto (fun l => Graphon.cutNormDiff (W c)
      (markedGraphon (B l c) (hsymm l c) (hbounds l c) (marks l) (hmeas l)))
      atTop (𝓝 0))
    (hmasses : ∀ l i, Tendsto (fun n => finiteMarkMass (labels l n) i)
      atTop (𝓝 (μ.real ((marks l) ⁻¹' {i}))))
    (hC4 : ∀ l c, ∃ L : ℝ,
      Tendsto (fun n => finiteC4 (fun x y => A n c x y -
        B l c (labels l n x) (labels l n y))) atTop (𝓝 L) ∧
      L ≤ 8 * Graphon.cutNormDiff (W c)
        (markedGraphon (B l c) (hsymm l c) (hbounds l c) (marks l) (hmeas l))) :
    FiniteCommonCutConverges μ A hAsymm hA W := by
  classical
  intro ε hε
  let a : ℝ := ε / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let δ : ℝ := min (a / 2) (a ^ 4 / 16)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ᶠ l in atTop, ∀ c,
      Graphon.cutNormDiff (W c)
        (markedGraphon (B l c) (hsymm l c) (hbounds l c) (marks l) (hmeas l)) < δ := by
    rw [Filter.eventually_all]
    intro c
    exact (tendsto_order.mp (happrox c)).2 δ hδ
  obtain ⟨l, hl⟩ := hsmall.exists
  have hW (c : Fin r) : Graphon.cutNormDiff (W c)
      (markedGraphon (B l c) (hsymm l c) (hbounds l c) (marks l) (hmeas l)) ≤ a := by
    have hd : δ ≤ a / 2 := min_le_left _ _
    linarith [hl c]
  have hfour : ∀ᶠ n in atTop, ∀ c, finiteC4 (fun x y => A n c x y -
      B l c (labels l n x) (labels l n y)) ≤ a ^ 4 := by
    rw [Filter.eventually_all]
    intro c
    obtain ⟨L, hL, hbound⟩ := hC4 l c
    have hLlt : L < a ^ 4 := by
      have hd : δ ≤ a ^ 4 / 16 := min_le_right _ _
      have hap : 0 < a ^ 4 := pow_pos ha _
      nlinarith [hl c]
    exact ((tendsto_order.mp hL).2 (a ^ 4) hLlt).mono fun _ h => h.le
  have hmasslim : Tendsto (fun n => ∑ i : Fin (k l),
      |finiteMarkMass (labels l n) i - μ.real ((marks l) ⁻¹' {i})|) atTop (𝓝 0) := by
    have ht (i : Fin (k l)) := ((hmasses l i).sub_const (μ.real ((marks l) ⁻¹' {i}))).abs
    simpa using tendsto_finsetSum Finset.univ (fun i _ => ht i)
  have hmasssmall : ∀ᶠ n in atTop, (∑ i : Fin (k l),
      |finiteMarkMass (labels l n) i - μ.real ((marks l) ⁻¹' {i})|) ≤ a / 2 :=
    ((tendsto_order.mp hmasslim).2 (a / 2) (by positivity)).mono fun _ h => h.le
  filter_upwards [hnonempty, hfour, hmasssmall] with n hn hfour hmasssmall
  let := hn
  have hU (c : Fin r) : Graphon.cutNormDiff
      (markedGraphon (μ := uniformFiniteMeasure (V n)) (A n c) (hAsymm n c) (hA n c)
        id measurable_id)
      (markedGraphon (B l c) (hsymm l c) (hbounds l c) (labels l n) Measurable.of_discrete) ≤ a :=
    matrix_cutNormDiff_le_of_C4_le uniformFiniteMeasure_singleton
      (A n c) (hAsymm n c) (hA n c) (B l c) (hsymm l c) (hbounds l c)
      (labels l n) Measurable.of_discrete ha.le (hfour c)
  have hm : (∑ i : Fin (k l),
      |(uniformFiniteMeasure (V n)).real ((labels l n) ⁻¹' {i}) -
        μ.real ((marks l) ⁻¹' {i})|) ≤ a / 2 := by
    simpa only [uniformFiniteMeasure_mark_mass] using hmasssmall
  obtain ⟨π, hπ⟩ := exists_common_coupling_of_step_approximation
    (fun c => markedGraphon (μ := uniformFiniteMeasure (V n)) (A n c)
      (hAsymm n c) (hA n c) id measurable_id) W
    (B l) (hsymm l) (hbounds l) (labels l n) (marks l) Measurable.of_discrete
    (hmeas l) hU hW hm
  refine ⟨hn, π, fun c => (hπ c).trans_lt ?_⟩
  dsimp [a]
  linarith

end Convergence

end ComponentTransfer.Realization
