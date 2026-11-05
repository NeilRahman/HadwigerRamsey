import HadwigerRamsey4Col.TransferCompactness
import HadwigerRamsey4Col.TransferRegularity

/-!
Common finite nets. The equipartition rerounding and finite-grid calculations
adapt Graphon.Compactness, Copyright (c) 2026 Cameron Freer, Apache 2.0;
see vendor/graphon/LICENSE.
-/

open MeasureTheory Set Filter Finset Graphon
open scoped BigOperators Topology Classical ENNReal

namespace HadwigerRamsey4Col.Transfer

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- The equipartition in step rerounding is chosen independently of all
coefficient matrices, hence may be shared by every colour. -/
theorem common_step_reround (P : MeasurablePartition α μ) {q : ℕ} (hq : 0 < q) :
    ∃ Q : MeasurablePartition α μ, Q.parts.card = q ∧
      (∀ A ∈ Q.parts, μ A = (1 : ℝ≥0∞)/q) ∧
      ∀ c : Set α → Set α → ℝ,
        ∀ hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S,
        ∀ hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Icc (0 : ℝ) 1,
        ∃ (cQ : Set α → Set α → ℝ)
          (hcQ_symm : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ A B = cQ B A)
          (hcQ_mem : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ A B ∈ Icc (0 : ℝ) 1),
          cutNormDiff (mkStepGraphon P c hc_symm hc_mem)
            (mkStepGraphon Q cQ hcQ_symm hcQ_mem) ≤ 2*(P.parts.card : ℝ)/q := by
  classical
  obtain ⟨Q, hQcard, hQmu, bad, hbad_meas, hbad_le, hrefine⟩ :=
    exists_equipartition_almost_refining P hq
  -- `Q` is nonempty (it has `q > 0` cells), giving a fallback parent `S₀ ∈ P.parts`.
  have hQne : Q.parts.Nonempty := by rw [← Finset.card_pos, hQcard]; exact hq
  obtain ⟨A₀, hA₀⟩ := hQne
  obtain ⟨S₀, hS₀, -⟩ := hrefine A₀ hA₀
  -- For each `Q`-cell `A`, pick a parent `P`-cell `par A` with `A \ bad ⊆ par A`.
  choose par hpar_mem hpar_sub using hrefine
  -- Total parent map (fallback to `S₀` off `Q.parts`, never actually used a.e.).
  set parentOf : Set α → Set α := fun A => if hA : A ∈ Q.parts then par A hA else S₀
    with hpar_def
  have hparentOf_mem : ∀ A, parentOf A ∈ P.parts := by
    intro A
    simp only [hpar_def]
    by_cases hA : A ∈ Q.parts
    · rw [dif_pos hA]; exact hpar_mem A hA
    · rw [dif_neg hA]; exact hS₀
  have hparentOf_sub : ∀ A, A ∈ Q.parts → A \ bad ⊆ parentOf A := by
    intro A hA
    simp only [hpar_def]
    rw [dif_pos hA]; exact hpar_sub A hA
  refine ⟨Q,hQcard,hQmu,?_⟩
  intro c hc_symm hc_mem
  -- Re-rounded coefficients: inherit the parent `P`-cell coefficient.
  set cQ : Set α → Set α → ℝ := fun A B => c (parentOf A) (parentOf B) with hcQ_def
  have hcQ_symm : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ A B = cQ B A := by
    intro A _ B _
    simp only [hcQ_def]
    exact hc_symm _ (hparentOf_mem A) _ (hparentOf_mem B)
  have hcQ_mem : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ A B ∈ Set.Icc 0 1 := by
    intro A _ B _
    simp only [hcQ_def]
    exact hc_mem _ (hparentOf_mem A) _ (hparentOf_mem B)
  refine ⟨cQ, hcQ_symm, hcQ_mem, ?_⟩
  -- Connect the graphons' `AEEqFun`s to the underlying step functions.
  have hU_eq : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c hc_symm hc_mem).toAEEqFun p = mkStepFun P c p :=
    AEEqFun.coeFn_mk (mkStepFun P c) (mkStepFun_measurable P c).aestronglyMeasurable
  have hW_eq : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon Q cQ hcQ_symm hcQ_mem).toAEEqFun p = mkStepFun Q cQ p :=
    AEEqFun.coeFn_mk (mkStepFun Q cQ) (mkStepFun_measurable Q cQ).aestronglyMeasurable
  have hAcov : ∀ᵐ p ∂(μ.prod μ), ∃ A ∈ Q.parts, p.1 ∈ A :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst Q.ae_covers
  have hBcov : ∀ᵐ p ∂(μ.prod μ), ∃ B ∈ Q.parts, p.2 ∈ B :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd Q.ae_covers
  refine le_trans (cutNormDiff_le_of_ae_agree_off_strip _ _ bad hbad_meas ?_) ?_
  · -- Off the strip, both step graphons equal `c` of the shared parent cells.
    filter_upwards [hU_eq, hW_eq, hAcov, hBcov] with p hPeq hQeq hAc hBc h1 h2
    obtain ⟨A, hA, hpA⟩ := hAc
    obtain ⟨B, hB, hpB⟩ := hBc
    have hp1par : p.1 ∈ parentOf A := hparentOf_sub A hA ⟨hpA, h1⟩
    have hp2par : p.2 ∈ parentOf B := hparentOf_sub B hB ⟨hpB, h2⟩
    rw [hPeq, hQeq,
      mkStepFun_eq_at P c (hparentOf_mem A) (hparentOf_mem B)
        (Set.mem_prod.mpr ⟨hp1par, hp2par⟩),
      mkStepFun_eq_at Q cQ hA hB (Set.mem_prod.mpr ⟨hpA, hpB⟩)]
  · -- Convert the measure bound `μ bad ≤ P.card / q` to the real-valued estimate.
    have hqE : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
    have hne : ((P.parts.card : ℝ≥0∞) / q) ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hqE
    have hbad_toReal : (μ bad).toReal ≤ (P.parts.card : ℝ) / q := by
      calc (μ bad).toReal ≤ ((P.parts.card : ℝ≥0∞) / q).toReal :=
            ENNReal.toReal_mono hne hbad_le
        _ = (P.parts.card : ℝ) / q := by
            rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    rw [mul_div_assoc]
    linarith [hbad_toReal]


/-- Common finite regularity and common equipartition rerounding give a finite
net with one measure-preserving equivalence for every colour. -/
theorem common_finite_nets (r : ℕ) : HasCommonNets (μ := μ) (r := r) := by
  classical
  intro ε hε
  -- Parameters
  set ε₃ := ε / 3 with hε₃_def
  have hε₃ : ε₃ > 0 := by positivity
  set N := Nat.ceil (3 / ε) with hN_def
  have hN_pos : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have h1N_le : (1 : ℝ) / N ≤ ε₃ := by
    rw [hε₃_def]
    have hN_le : (3 / ε : ℝ) ≤ N := Nat.le_ceil (3 / ε)
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hN_pos) (by norm_num : (0:ℝ) < 3), one_mul]
    calc (3 : ℝ) = ε * (3 / ε) := by field_simp
      _ ≤ ε * N := by apply mul_le_mul_of_nonneg_left hN_le hε.le
  set m₀ := commonRegularityBound r ε₃ with hm₀_def
  set q := Nat.ceil (6 * (m₀ : ℝ) / ε) + 1 with hq_def
  have hq : 0 < q := by omega
  have hq_real : (0 : ℝ) < q := by exact_mod_cast hq
  -- q is large enough that 2 * m₀ / q ≤ ε/3
  have hεq : 6 * (m₀ : ℝ) ≤ ε * q := by
    have h1 : (6 * (m₀ : ℝ) / ε) ≤ q := by
      have hc := Nat.le_ceil (6 * (m₀ : ℝ) / ε)
      rw [hq_def]; push_cast; linarith
    calc 6 * (m₀ : ℝ) = ε * (6 * (m₀ : ℝ) / ε) := by field_simp
      _ ≤ ε * q := by apply mul_le_mul_of_nonneg_left h1 hε.le
  have h2m0q : 2 * (m₀ : ℝ) / q ≤ ε₃ := by
    rw [div_le_iff₀ hq_real, hε₃_def]; nlinarith [hεq]
  -- Fix a canonical equal-measure q-cell partition E (W-independent)
  obtain ⟨E, hEcard, hEmu, -⟩ :=
    exists_equipartition_almost_refining (trivialPartition (α := α) (μ := μ)) hq
  -- Injective enumeration of E's cells
  set eqE := (E.parts.equivFinOfCardEq hEcard).symm with heqE_def
  set ιE : Fin q → Set α := fun i => (eqE i : Set α) with hιE_def
  have hιE_mem : ∀ i, ιE i ∈ E.parts := fun i => (eqE i).2
  have hιE_inj : Function.Injective ιE := fun i j h => eqE.injective (Subtype.ext h)
  have hιE_mu : ∀ i, μ (ιE i) = (1 : ℝ≥0∞) / q := fun i => hEmu _ (hιE_mem i)
  let toCoeff : (↑E.parts → ↑E.parts → Fin (N + 1)) → Set α → Set α → ℝ :=
    fun f S T =>
      if hS : S ∈ E.parts then
        if hT : T ∈ E.parts then
          ((f ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) + (f ⟨T, hT⟩ ⟨S, hS⟩ : ℕ)) / (2 * N)
        else 0
      else 0
  have htoCoeff_symm : ∀ f, ∀ S ∈ E.parts, ∀ T ∈ E.parts,
      toCoeff f S T = toCoeff f T S := by
    intro f S hS T hT
    simp only [toCoeff, hS, hT, dif_pos]
    ring
  have htoCoeff_mem : ∀ f, ∀ S ∈ E.parts, ∀ T ∈ E.parts,
      toCoeff f S T ∈ Set.Icc 0 1 := by
    intro f S hS T hT
    simp only [toCoeff, hS, hT, dif_pos, Set.mem_Icc]
    refine ⟨by positivity, ?_⟩
    have h1 : (f ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) ≤ N := by omega
    have h2 : (f ⟨T, hT⟩ ⟨S, hS⟩ : ℕ) ≤ N := by omega
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * N)]
    have h1' : (↑(f ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h1
    have h2' : (↑(f ⟨T, hT⟩ ⟨S, hS⟩ : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h2
    linarith
  let netMap : (Fin r → ↑E.parts → ↑E.parts → Fin (N+1)) → Tuple (μ := μ) (r := r) :=
    fun f c => mkStepGraphon E (toCoeff (f c)) (htoCoeff_symm (f c)) (htoCoeff_mem (f c))
  let net : Finset (Tuple (μ := μ) (r := r)) := Finset.univ.image netMap
  refine ⟨net,?_⟩
  intro W
  obtain ⟨P_W,hP_W_card,hP_W_close⟩ := common_regularity W ε₃ hε₃
  have hRA_symm (c : Fin r) : ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts,
      rectAverage (W c) S T = rectAverage (W c) T S := by
    intro S hS T hT
    exact rectAverage_symm (W c) S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
  have hRA_mem (c : Fin r) : ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts,
      rectAverage (W c) S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    exact rectAverage_mem_Icc (W c) S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
  let V_avg : Fin r → Graphon α μ := fun c =>
    mkStepGraphon P_W (rectAverage (W c)) (hRA_symm c) (hRA_mem c)
  have hStepEq (c : Fin r) : stepify P_W (W c) = V_avg c := by
    apply Graphon.ext
    apply SymmKernel.ext
    apply AEEqFun.ext
    filter_upwards [stepify_ae P_W (W c),
      AEEqFun.coeFn_mk (mkStepFun P_W (rectAverage (W c)))
        (mkStepFun_measurable P_W (rectAverage (W c))).aestronglyMeasurable] with p hp hq
    exact hp.trans hq.symm
  obtain ⟨Q,hQcard,hQmu,hQ⟩ := common_step_reround P_W hq
  choose cQ hcQ_symm hcQ_mem hbound using fun c : Fin r =>
    hQ (rectAverage (W c)) (hRA_symm c) (hRA_mem c)
  let V_Q : Fin r → Graphon α μ := fun c => mkStepGraphon Q (cQ c) (hcQ_symm c) (hcQ_mem c)
  have hReround (c) : cutNormDiff (V_avg c) (V_Q c) ≤ ε₃ := by
    exact (hbound c).trans ((by gcongr :
      2*(P_W.parts.card : ℝ)/q ≤ 2*(m₀ : ℝ)/q).trans h2m0q)
  let roundCQ (c : Fin r) : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ Q.parts then
      if hT : T ∈ Q.parts then (Nat.floor (cQ c S T*N) : ℝ)/N else 0
    else 0
  have hroundCQ_symm (c) : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts,
      roundCQ c S T = roundCQ c T S := by
    intro S hS T hT
    simp only [roundCQ,hS,hT,dif_pos]
    rw [hcQ_symm c S hS T hT]
  have hroundCQ_mem (c) : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts,
      roundCQ c S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    simp only [roundCQ,hS,hT,dif_pos,Set.mem_Icc]
    have hc := hcQ_mem c S hS T hT
    refine ⟨by positivity,?_⟩
    rw [div_le_one (Nat.cast_pos.mpr hN_pos)]
    exact_mod_cast Nat.floor_le_of_le (by exact_mod_cast
      (by nlinarith [hc.2] : cQ c S T*N ≤ (N : ℝ)))
  have hroundCQ_close (c) : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts,
      |cQ c S T-roundCQ c S T| ≤ 1/(N : ℝ) := by
    intro S hS T hT
    simp only [roundCQ,hS,hT,dif_pos]
    have hc := hcQ_mem c S hS T hT
    have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have hnn : 0 ≤ cQ c S T*N := mul_nonneg hc.1 (Nat.cast_nonneg N)
    have hfloor := Nat.floor_le hnn
    have hlt := Nat.lt_floor_add_one (cQ c S T*N)
    rw [abs_le]
    constructor
    · have hn : 0 ≤ cQ c S T-(Nat.floor (cQ c S T*N) : ℝ)/N := by
        rw [sub_nonneg,div_le_iff₀ hNp]
        exact hfloor
      have hi : (0 : ℝ) ≤ 1/N := by positivity
      linarith
    · rw [sub_le_iff_le_add,
        show 1/(N : ℝ)+(Nat.floor (cQ c S T*N) : ℝ)/N =
          ((Nat.floor (cQ c S T*N) : ℝ)+1)/N by ring,
        le_div_iff₀ hNp]
      exact hlt.le
  let V_QR : Fin r → Graphon α μ := fun c =>
    mkStepGraphon Q (roundCQ c) (hroundCQ_symm c) (hroundCQ_mem c)
  have hGrid (c) : cutNormDiff (V_Q c) (V_QR c) ≤ ε₃ :=
    (cutNormDiff_mkStepGraphon_le Q (cQ c) (roundCQ c) (hcQ_symm c) (hcQ_mem c)
      (hroundCQ_symm c) (hroundCQ_mem c) (1/N) (hroundCQ_close c)).trans h1N_le
  let eqQ := (Q.parts.equivFinOfCardEq hQcard).symm
  let ιQ : Fin q → Set α := fun i => (eqQ i : Set α)
  have hιQ_mem (i) : ιQ i ∈ Q.parts := (eqQ i).2
  have hιQ_inj : Function.Injective ιQ := fun i j h => eqQ.injective (Subtype.ext h)
  have hιQ_mu (i) : μ (ιQ i) = (1 : ℝ≥0∞)/q := hQmu _ (hιQ_mem i)
  have hμmatch (i) : μ (ιE i) = μ (ιQ i) := (hιE_mu i).trans (hιQ_mu i).symm
  obtain ⟨e,he,halign⟩ := MeasurePreserving.exists_controlled_cell_alignment E Q ιE ιQ
    hιE_mem hιQ_mem hιE_inj hιQ_inj hμmatch
  let f : Fin r → ↑E.parts → ↑E.parts → Fin (N+1) := fun c S T =>
    ⟨Nat.floor (cQ c (ιQ (eqE.symm S)) (ιQ (eqE.symm T))*N), by
      have hc := hcQ_mem c (ιQ (eqE.symm S)) (hιQ_mem _) (ιQ (eqE.symm T)) (hιQ_mem _)
      apply Nat.lt_succ_of_le
      exact Nat.floor_le_of_le (by exact_mod_cast
        (by nlinarith [hc.2] : cQ c (ιQ (eqE.symm S)) (ιQ (eqE.symm T))*N ≤ (N : ℝ)))⟩
  have hCoeffEq (c) (S) (hS : S ∈ E.parts) (T) (hT : T ∈ E.parts) :
      toCoeff (f c) S T = roundCQ c (ιQ (eqE.symm ⟨S,hS⟩)) (ιQ (eqE.symm ⟨T,hT⟩)) := by
    have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
    simp only [toCoeff,hS,hT,dif_pos,f,roundCQ,hιQ_mem]
    rw [hcQ_symm c (ιQ (eqE.symm ⟨T,hT⟩)) (hιQ_mem _)
      (ιQ (eqE.symm ⟨S,hS⟩)) (hιQ_mem _)]
    field_simp
    ring
  have hAlignAll : ∀ᵐ x ∂μ, ∀ i, x ∈ ιE i → e x ∈ ιQ i := (ae_all_iff).mpr halign
  have hEF : ∀ᵐ p ∂μ.prod μ, ∀ i, p.1 ∈ ιE i → e p.1 ∈ ιQ i :=
    Measure.quasiMeasurePreserving_fst.ae hAlignAll
  have hES : ∀ᵐ p ∂μ.prod μ, ∀ i, p.2 ∈ ιE i → e p.2 ∈ ιQ i :=
    Measure.quasiMeasurePreserving_snd.ae hAlignAll
  have hCovF : ∀ᵐ p ∂μ.prod μ, ∃ S ∈ E.parts, p.1 ∈ S :=
    Measure.quasiMeasurePreserving_fst.ae E.ae_covers
  have hCovS : ∀ᵐ p ∂μ.prod μ, ∃ S ∈ E.parts, p.2 ∈ S :=
    Measure.quasiMeasurePreserving_snd.ae E.ae_covers
  have hExact (c) : pullback (V_QR c) e he = netMap f c := by
    apply Graphon.ext
    apply SymmKernel.ext
    apply AEEqFun.ext
    have hNet : ∀ᵐ p ∂μ.prod μ, (netMap f c).toAEEqFun p = mkStepFun E (toCoeff (f c)) p :=
      AEEqFun.coeFn_mk _ _
    have hVR : ∀ᵐ p ∂μ.prod μ, (V_QR c).toAEEqFun p = mkStepFun Q (roundCQ c) p :=
      AEEqFun.coeFn_mk _ _
    have hImage := (he.prod he).quasiMeasurePreserving.ae hVR
    filter_upwards [pullback_ae (V_QR c) e he,hNet,hImage,hCovF,hCovS,hEF,hES]
      with p hp hn hi ⟨S₁,hS₁,hpS₁⟩ ⟨S₂,hS₂,hpS₂⟩ hef hes
    have hi₁ : p.1 ∈ ιE (eqE.symm ⟨S₁,hS₁⟩) := by simpa [ιE] using hpS₁
    have hi₂ : p.2 ∈ ιE (eqE.symm ⟨S₂,hS₂⟩) := by simpa [ιE] using hpS₂
    change (V_QR c).toAEEqFun (e p.1,e p.2) = mkStepFun Q (roundCQ c) (e p.1,e p.2) at hi
    rw [hp,hi,hn,
      mkStepFun_eq_at Q (roundCQ c) (hιQ_mem _) (hιQ_mem _)
        (Set.mem_prod.mpr ⟨hef _ hi₁,hes _ hi₂⟩),
      mkStepFun_eq_at E (toCoeff (f c)) hS₁ hS₂ (Set.mem_prod.mpr ⟨hpS₁,hpS₂⟩),
      hCoeffEq c S₁ hS₁ S₂ hS₂]
  refine ⟨netMap f,Finset.mem_image.mpr ⟨f,Finset.mem_univ _,rfl⟩,e,he,fun c => ?_⟩
  rw [← hExact c]
  have h₁ : cutNormDiff (pullback (W c) e he) (pullback (V_avg c) e he) ≤ ε₃ := by
    rw [cutNormDiff_pullback_measurableEquiv, ← hStepEq c]
    exact hP_W_close c
  have h₂ : cutNormDiff (pullback (V_avg c) e he) (pullback (V_Q c) e he) ≤ ε₃ := by
    rw [cutNormDiff_pullback_measurableEquiv]
    exact hReround c
  have h₃ : cutNormDiff (pullback (V_Q c) e he) (pullback (V_QR c) e he) ≤ ε₃ := by
    rw [cutNormDiff_pullback_measurableEquiv]
    exact hGrid c
  have ht₁ := cutNormDiff_triangle (pullback (W c) e he) (pullback (V_avg c) e he)
    (pullback (V_QR c) e he)
  have ht₂ := cutNormDiff_triangle (pullback (V_avg c) e he) (pullback (V_Q c) e he)
    (pullback (V_QR c) e he)
  dsimp only [ε₃] at *
  linarith

end HadwigerRamsey4Col.Transfer
