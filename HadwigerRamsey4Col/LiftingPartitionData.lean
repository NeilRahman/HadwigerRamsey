import HadwigerRamsey4Col.LiftingRegion
import HadwigerRamsey4Col.LiftingPositivePartition

open scoped Classical Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

set_option backward.isDefEq.respectTransparency false

namespace HadwigerRamsey4Col.Realization

lemma cond_real_of_subset {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (S A : Set α) (hS : MeasurableSet S) (hAS : A ⊆ S) :
    (cond μ S).real A = μ.real A / μ.real S := by
  simp only [measureReal_def, cond_apply hS, Set.inter_eq_right.mpr hAS,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

lemma restrictGraphon_rectIntegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] (W : Graphon α μ)
    (S A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (restrictGraphon W S).toSymmKernel.rectIntegral A B =
      W.toSymmKernel.rectIntegral (A ∩ S) (B ∩ S) / (μ.real S)^2 := by
  unfold SymmKernel.rectIntegral
  have heq := restrictGraphon_ae W S
  rw [integral_congr_ae (ae_restrict_of_ae heq)]
  rw [prod_cond_eq, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_restrict (hA.prod hB), Set.prod_inter_prod]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, smul_eq_mul]
  change (μ.real S)⁻¹ ^ 2 * _ = _
  rw [inv_pow, div_eq_mul_inv, mul_comm]

/-- The finite partitions needed in entropy lifting, after selecting the
ambient measurable region. Every retained class has positive limiting mass;
the active classes reproduce the prescribed sets, even when leftovers are null. -/
structure LiftingPartitionData {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r k : ℕ}
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (W : Fin r → Graphon α μ) (S : Set α) (A : Fin k → Set α)
    [IsProbabilityMeasure (cond μ S)] where
  region : ∀ n, Finset (Fin (N n))
  parts : ℕ
  active : Fin k ↪ Fin parts
  labels : ∀ n, Fin (region n).card → Fin parts
  masses : Fin parts → ℝ
  masses_pos : ∀ j, 0 < masses j
  masses_tendsto : ∀ j, Tendsto (fun n => classMass (labels n) j) atTop (𝓝 (masses j))
  active_mass : ∀ i, masses (active i) = μ.real (A i) / μ.real S
  density_tendsto : ∀ c i j,
    Tendsto (fun n => blockDensity (selectedGraph (G n c) (region n)) (labels n)
      (active i) (active j)) atTop
      (𝓝 ((W c).toSymmKernel.rectIntegral (A i) (A j) /
        (μ.real (A i) * μ.real (A j))))
  region_mass : Tendsto (fun n => ((region n).card : ℝ) / (N n : ℝ))
    atTop (𝓝 (μ.real S))
  region_order : Tendsto (fun n => (region n).card) atTop atTop
  region_converges : FiniteGraphCommonCutConverges (cond μ S) (fun n => (region n).card)
    (fun n c => selectedGraph (G n c) (region n)) (fun c => restrictGraphon (W c) S)

/-- Active class sizes, normalized by the original graph order, converge to
the original (unnormalized) measures. -/
theorem LiftingPartitionData.active_global_mass_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {r k : ℕ} {N : ℕ → ℕ} {G : ∀ n, Fin r → SimpleGraph (Fin (N n))}
    {W : Fin r → Graphon α μ} {S : Set α} {A : Fin k → Set α}
    [IsProbabilityMeasure (cond μ S)] (D : LiftingPartitionData μ N G W S A)
    (hN : Tendsto N atTop atTop) (hSpos : 0 < μ.real S) (i : Fin k) :
    Tendsto (fun n => ((classVertices (D.labels n) (D.active i)).card : ℝ) / (N n : ℝ))
      atTop (𝓝 (μ.real (A i))) := by
  have hh := (D.masses_tendsto (D.active i)).mul D.region_mass
  rw [D.active_mass, div_mul_cancel₀ _ hSpos.ne'] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_gt_atTop 0, D.region_order.eventually_gt_atTop 0] with n hn hm
  have hn' : (N n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : ((D.region n).card : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  change ((classVertices (D.labels n) (D.active i)).card : ℝ) / ((D.region n).card : ℝ) *
    (((D.region n).card : ℝ) / (N n : ℝ)) = _
  field_simp

/-- The target densities lie in the closed unit interval, including the
endpoint one that gives an infinite entropy contribution. -/
theorem LiftingPartitionData.density_mem_Icc
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {r k : ℕ} {N : ℕ → ℕ} {G : ∀ n, Fin r → SimpleGraph (Fin (N n))}
    {W : Fin r → Graphon α μ} {S : Set α} {A : Fin k → Set α}
    [IsProbabilityMeasure (cond μ S)] (D : LiftingPartitionData μ N G W S A)
    (c : Fin r) (i j : Fin k) :
    (W c).toSymmKernel.rectIntegral (A i) (A j) /
      (μ.real (A i) * μ.real (A j)) ∈ Icc (0 : ℝ) 1 := by
  apply isClosed_Icc.mem_of_tendsto (D.density_tendsto c i j)
  exact Eventually.of_forall fun n => ⟨blockDensity_nonneg _ _ _ _,blockDensity_le_one _ _ _ _⟩

/-- Realize a positive measurable region and all prescribed positive subsets
in it, omitting every null partition class before applying the finite minor
bound. Only a nonempty family of prescribed sets is required. -/
theorem exists_lifting_partition_data {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r k : ℕ} (hr : 2 ≤ r) (hk : 0 < k)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (hconv : FiniteGraphCommonCutConverges μ N G W)
    (S : Set α) (hS : MeasurableSet S) (hSpos : 0 < μ.real S)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hsub : ∀ i, A i ⊆ S) (hpos : ∀ i, 0 < μ.real (A i))
    [IsProbabilityMeasure (cond μ S)] :
    Nonempty (LiftingPartitionData μ N G W S A) := by
  let c₀ : Fin r := ⟨0,by omega⟩
  obtain ⟨T,hmass,horder,hcut⟩ := exists_region_realization μ c₀ N hN G W hconv S hS hSpos
  have hcondpos (i : Fin k) : 0 < (cond μ S).real (A i) := by
    rw [cond_real_of_subset S (A i) hS (hsub i)]
    exact div_pos (hpos i) hSpos
  obtain ⟨l,mark,f,hmark,hpositive,hactive⟩ :=
    exists_positive_partition_extension (cond μ S) hk A hA hdisjoint hcondpos
  let B : Fin l → Set α := fun j => mark ⁻¹' {j}
  have hB (j : Fin l) : MeasurableSet (B j) := hmark (measurableSet_singleton j)
  have hdB : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hi' : mark x = i := hi
    have hj' : mark x = j := hj
    exact hij (hi'.symm.trans hj')
  have hcB : (⋃ j, B j) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨mark x,rfl⟩
  obtain ⟨labels,hsizes,hdensity,_⟩ := HadwigerRamsey4Col.lemma7 (cond μ S) hr
    (fun n => (T n).card) horder (fun n c => selectedGraph (G n c) (T n))
    (fun c => restrictGraphon (W c) S) hcut B hB hdB hcB hpositive
  have hactive_real (i : Fin k) : (cond μ S).real (B (f i)) = μ.real (A i) / μ.real S := by
    rw [measureReal_def, measure_congr (hactive i)]
    exact cond_real_of_subset S (A i) hS (hsub i)
  refine ⟨{
    region := T
    parts := l
    active := f
    labels := labels
    masses := fun j => (cond μ S).real (B j)
    masses_pos := hpositive
    masses_tendsto := hsizes
    active_mass := hactive_real
    density_tendsto := ?_
    region_mass := hmass
    region_order := horder
    region_converges := hcut
  }⟩
  intro c i j
  have hd := hdensity c (f i) (f j)
  have hrect : (restrictGraphon (W c) S).toSymmKernel.rectIntegral (B (f i)) (B (f j)) =
      (W c).toSymmKernel.rectIntegral (A i) (A j) / (μ.real S)^2 := by
    rw [rectIntegral_congr_ae_sets (restrictGraphon (W c) S) (hactive i) (hactive j),
      restrictGraphon_rectIntegral (W c) S (A i) (A j) (hA i) (hA j),
      Set.inter_eq_left.mpr (hsub i), Set.inter_eq_left.mpr (hsub j)]
  rw [hrect,hactive_real i,hactive_real j] at hd
  convert hd using 1
  congr 1
  field_simp [hSpos.ne', (hpos i).ne', (hpos j).ne'] <;> ring

end HadwigerRamsey4Col.Realization
