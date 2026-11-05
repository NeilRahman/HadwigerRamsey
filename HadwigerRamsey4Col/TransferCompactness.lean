import Graphon.Compactness
import HadwigerRamsey4Col.RealizationCommonMaps

open MeasureTheory Filter Set Finset
open scoped BigOperators Topology Classical

namespace HadwigerRamsey4Col.Transfer

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]
    {r : ℕ}

abbrev Tuple := Fin r → Graphon α μ

/-- A finite common-equivalence net controls all colours using one map. -/
def HasCommonNets : Prop := ∀ ε : ℝ, 0 < ε →
  ∃ S : Finset (Tuple (μ := μ) (r := r)), ∀ U : Tuple (μ := μ) (r := r),
    ∃ V ∈ S, ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
      ∀ c, Graphon.cutNormDiff (Graphon.pullback (U c) e he) (V c) ≤ ε

lemma pullback_equiv_cancel (U : Graphon α μ) (e : α ≃ᵐ α)
    (he : MeasurePreserving e μ μ) :
    Graphon.pullback (Graphon.pullback U e he) e.symm (he.symm e) = U := by
  rw [Graphon.pullback_pullback]
  apply Graphon.ext
  apply SymmKernel.ext
  apply AEEqFun.ext
  filter_upwards [Graphon.pullback_ae U (e ∘ e.symm) (he.comp (he.symm e))] with p hp
  simpa using hp

lemma common_close_comp (U V C : Tuple (μ := μ) (r := r))
    (a b : α ≃ᵐ α) (ha : MeasurePreserving a μ μ) (hb : MeasurePreserving b μ μ)
    {ε : ℝ}
    (hU : ∀ c, Graphon.cutNormDiff (Graphon.pullback (U c) a ha) (C c) ≤ ε)
    (hV : ∀ c, Graphon.cutNormDiff (Graphon.pullback (V c) b hb) (C c) ≤ ε) :
    ∀ c, Graphon.cutNormDiff
      (Graphon.pullback (U c) (b.symm.trans a) (ha.comp (hb.symm b))) (V c) ≤ 2*ε := by
  intro c
  have h := Graphon.cutNormDiff_triangle (Graphon.pullback (U c) a ha) (C c)
    (Graphon.pullback (V c) b hb)
  rw [Graphon.cutNormDiff_symm (C c)] at h
  have hbnd : Graphon.cutNormDiff (Graphon.pullback (U c) a ha)
      (Graphon.pullback (V c) b hb) ≤ 2*ε := by linarith [hU c,hV c]
  have hi := Graphon.cutNormDiff_pullback_measurableEquiv
    (Graphon.pullback (U c) a ha) (Graphon.pullback (V c) b hb) b.symm (hb.symm b)
  rw [pullback_equiv_cancel, Graphon.pullback_pullback] at hi
  exact hi.trans_le hbnd

private structure Cluster (W : ℕ → Tuple (μ := μ) (r := r)) (ε : ℝ) where
  indices : Set ℕ
  infinite : indices.Infinite
  centre : Tuple (μ := μ) (r := r)
  close : ∀ n ∈ indices, ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
    ∀ c, Graphon.cutNormDiff (Graphon.pullback (W n c) e he) (centre c) ≤ ε

private theorem refine_cluster (hnets : HasCommonNets (μ := μ) (r := r))
    (W : ℕ → Tuple (μ := μ) (r := r)) (A : Set ℕ) (hA : A.Infinite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Cluster W ε, C.indices ⊆ A := by
  classical
  obtain ⟨S,hS⟩ := hnets ε hε
  choose g hg hgclose using fun n => hS (W n)
  let g' : A → (S : Set (Tuple (μ := μ) (r := r))) := fun n => ⟨g n,hg n⟩
  haveI : Infinite A := Set.infinite_coe_iff.mpr hA
  haveI : Finite (S : Set (Tuple (μ := μ) (r := r))) := S.finite_toSet.to_subtype
  obtain ⟨⟨V,hV⟩,hinf⟩ := Finite.exists_infinite_fiber g'
  let B := Subtype.val '' (g' ⁻¹' {⟨V,hV⟩})
  have hB : B.Infinite := (Set.infinite_coe_iff.mp hinf).image Subtype.val_injective.injOn
  refine ⟨⟨B,hB,V,?_⟩,?_⟩
  · rintro n ⟨⟨n',hn'⟩,hmem,rfl⟩
    have he : g n' = V := by simpa [g'] using hmem
    rw [← he]
    exact hgclose n'
  · rintro n ⟨⟨n',hn'⟩,hmem,rfl⟩
    exact hn'

/-- A common finite net at every tolerance gives a subsequence whose successive
terms are close under one measurable equivalence for every colour. -/
theorem exists_rapid_common_subsequence
    (hnets : HasCommonNets (μ := μ) (r := r)) (W : ℕ → Tuple (μ := μ) (r := r)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ), ∀ c,
        Graphon.cutNormDiff (Graphon.pullback (W (φ (k+1)) c) e he) (W (φ k) c) ≤
          (1 : ℝ)/2^k := by
  let ε : ℕ → ℝ := fun k => 1/2^(k+1)
  have hε (k) : 0 < ε k := by dsimp [ε]; positivity
  choose C hCsub using fun (A : Set ℕ) (hA : A.Infinite) (k : ℕ) =>
    refine_cluster hnets W A hA (hε k)
  let build : ∀ k, Cluster W (ε k) :=
    Nat.rec (C Set.univ Set.infinite_univ 0)
      (fun k prev => C prev.indices prev.infinite (k+1))
  let J := fun k => (build k).indices
  have hJinf (k) : (J k).Infinite := (build k).infinite
  have hJnest (k) : J (k+1) ⊆ J k := hCsub (build k).indices (build k).infinite (k+1)
  choose next hnextmem hnextgt using fun k bound => (hJinf k).exists_gt bound
  let φ : ℕ → ℕ := Nat.rec (next 0 0) (fun k prev => next (k+1) prev)
  have hφmono : StrictMono φ := strictMono_nat_of_lt_succ (fun k => hnextgt (k+1) (φ k))
  have hφmem (k) : φ k ∈ J k := by
    cases k with
    | zero => exact hnextmem 0 0
    | succ k => exact hnextmem (k+1) (φ k)
  refine ⟨φ,hφmono,fun k => ?_⟩
  obtain ⟨a,ha,haClose⟩ := (build k).close (φ (k+1)) (hJnest k (hφmem (k+1)))
  obtain ⟨b,hb,hbClose⟩ := (build k).close (φ k) (hφmem k)
  refine ⟨b.symm.trans a,ha.comp (hb.symm b),fun c => ?_⟩
  have h := common_close_comp (W (φ (k+1))) (W (φ k)) (build k).centre a b ha hb haClose hbClose c
  convert h using 1
  dsimp [ε]
  rw [pow_succ]
  field_simp

/-- Common finite nets yield compactness with a single alignment for all
colours. Coordinate limits use the public scalar summable cut-norm theorem. -/
theorem compact_of_common_nets
    (hnets : HasCommonNets (μ := μ) (r := r)) (W : ℕ → Tuple (μ := μ) (r := r)) :
    ∃ (L : Tuple (μ := μ) (r := r)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → α ≃ᵐ α) (he : ∀ n, MeasurePreserving (e n) μ μ), ∀ c,
        Tendsto (fun n => Graphon.cutNormDiff (Graphon.pullback (W (φ n) c) (e n) (he n)) (L c))
          atTop (𝓝 0) := by
  obtain ⟨φ,hφ,hrapid⟩ := exists_rapid_common_subsequence hnets W
  choose σ hσ hσclose using hrapid
  let e : ℕ → α ≃ᵐ α := Nat.rec (MeasurableEquiv.refl α) (fun k prev => prev.trans (σ k))
  have he (k) : MeasurePreserving (e k) μ μ := by
    induction k with
    | zero => exact MeasurePreserving.id μ
    | succ k ih => exact (hσ k).comp ih
  let δ : ℕ → ℝ := fun k => 1/2^k
  have hδsum : Summable δ := by
    have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ)/2 < 1)
    simpa only [δ,div_pow,one_pow] using h
  have hδ (k) : 0 ≤ δ k := by dsimp [δ]; positivity
  have hstep (c : Fin r) (k) : Graphon.cutNormDiff
      (Graphon.pullback (W (φ (k+1)) c) (e (k+1)) (he (k+1)))
      (Graphon.pullback (W (φ k) c) (e k) (he k)) ≤ δ k := by
    change Graphon.cutNormDiff
      (Graphon.pullback (W (φ (k+1)) c) (σ k ∘ e k) ((hσ k).comp (he k))) _ ≤ δ k
    rw [← Graphon.pullback_pullback (W (φ (k+1)) c) (σ k) (hσ k) (e k) (he k)]
    rw [Graphon.cutNormDiff_pullback_measurableEquiv]
    exact hσclose k c
  have hL (c : Fin r) : ∃ L : Graphon α μ, Tendsto (fun n => Graphon.cutNormDiff
      (Graphon.pullback (W (φ n) c) (e n) (he n)) L) atTop (𝓝 0) := by
    obtain ⟨L,hL⟩ := Graphon.exists_cutNormDiff_limit_of_summable
      (fun n => Graphon.pullback (W (φ n) c) (e n) (he n)) δ hδ hδsum (hstep c)
    refine ⟨L,?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N,hN⟩ := hL ε hε
    exact ⟨N,fun n hn => by simpa [Real.dist_eq,abs_of_nonneg (Graphon.cutNormDiff_nonneg _ _)] using hN n hn⟩
  choose L hL using hL
  exact ⟨L,φ,hφ,e,he,hL⟩

end HadwigerRamsey4Col.Transfer
