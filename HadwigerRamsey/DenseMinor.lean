import HadwigerRamsey.DenseMinor.Cut

open scoped Classical
open Finset Real
namespace HadwigerRamsey
set_option maxHeartbeats 800000

/-- Lemma 3.4 (`denseMinor`). The reduction explicitly uses `bipMinor`. -/
theorem denseMinor (K : ℝ) (hK : 0 < K) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ n ≥ n₀, ∀ H : SimpleGraph (Fin n),
      (1-gamma)*(n.choose 2 : ℝ) ≤ H.edgeFinset.card →
      K*(n : ℝ)/sqrt (log (n : ℝ)) ≤ (hadwigerNumber H : ℝ) := by
  obtain ⟨delta,hd,N,hN,hbip⟩ := bipMinor (3*K) (by positivity)
  let L := max (N+1) (max 2 ⌈16/delta⌉₊)
  have hL2 : 2 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLN : N < L := by have := le_max_left (N+1) (max 2 ⌈16/delta⌉₊); omega
  have hLd : ⌈16/delta⌉₊ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  let gamma := delta/16
  have hg : 0 < gamma := by dsimp only [gamma]; positivity
  refine ⟨gamma,hg,3*L,by omega,?_⟩
  intro n hn H hedges
  let a := n/2
  have haL : L ≤ a := by dsimp only [a]; omega
  have ha2 : 2 ≤ a := hL2.trans haL
  have haN : N < a := hLN.trans_le haL
  have hn2a : 2*a ≤ n := by dsimp only [a]; omega
  have hn3a : n ≤ 3*a := by dsimp only [a] at *; omega
  have haR : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hda : 16 ≤ delta*(a : ℝ) := by
    have hh : 16/delta ≤ (a : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hLd.trans haL)
    have hh' := (div_le_iff₀ hd).mp hh
    nlinarith only [hh']
  let f : Fin (2*a) → Fin n := Fin.castLE hn2a
  have hf : Function.Injective f := Fin.castLE_injective hn2a
  let G := H.comap f
  let c := Existence.halfClass (m := a)
  let C := DenseMinor.cutGraph G c
  have hcard : ∀ i, (ThomasonUpper.classVertices c i).card = a := DenseMinor.half_card (by omega : 0 < a)
  have hmiss := DenseMinor.cross_missing_bound H f hf (by omega : 0 < a)
  change (C.edgeFinset.card : ℝ)+(n : ℝ)^2-2*H.edgeFinset.card ≥ (a : ℝ)^2 at hmiss
  have hcross : (1-delta)*(a : ℝ)^2 ≤ C.edgeFinset.card := by
    rw [Nat.cast_choose_two] at hedges
    have hn3aR : (n : ℝ) ≤ 3*(a : ℝ) := by exact_mod_cast hn3a
    have hsquare : (n : ℝ)^2 ≤ 9*(a : ℝ)^2 := by nlinarith only [hn3aR,hnR,haR]
    have hh1 := mul_le_mul_of_nonneg_left hsquare hg.le
    have hh2 := mul_le_mul_of_nonneg_right hda haR.le
    have hh3 := mul_nonneg hg.le hnR.le
    dsimp only [gamma] at hedges hh1 hh3
    nlinarith only [hedges,hmiss,hn3aR,hh1,hh2,hh3]
  have hbound := hbip (2*a) C (ThomasonUpper.classVertices c 0) (ThomasonUpper.classVertices c 1)
    (DenseMinor.cut_bipartite G c) (DenseMinor.classes_cover c)
    (by rw [hcard 0,hcard 1])
    (by rw [hcard 0]; exact haN.le)
    (by simpa only [hcard] using hcross)
  have hCG : hadwigerNumber C ≤ hadwigerNumber G := by
    apply cliqueMinor_le_hadwigerNumber
    exact (hadwigerNumber_hasCliqueMinor C).map_injective
      (SimpleGraph.Hom.ofLE (DenseMinor.cutGraph_le G c)) Function.injective_id
  have hGH : hadwigerNumber G ≤ hadwigerNumber H := hadwigerNumber_comap_le H f hf
  have hCH : (hadwigerNumber C : ℝ) ≤ hadwigerNumber H := by exact_mod_cast hCG.trans hGH
  have hrootA : 0 < sqrt (log (a : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast (by omega : 1 < a)))
  have hrootle : sqrt (log (a : ℝ)) ≤ sqrt (log (n : ℝ)) :=
    sqrt_le_sqrt (log_le_log haR (by exact_mod_cast (by dsimp [a]; omega : a ≤ n)))
  have hn3aR : (n : ℝ) ≤ 3*(a : ℝ) := by exact_mod_cast hn3a
  have hbound' : (3*K)*(a : ℝ)/sqrt (log (a : ℝ)) ≤ hadwigerNumber C := by
    simpa only [hcard] using hbound
  calc
    _ ≤ K*(3*(a : ℝ))/sqrt (log (n : ℝ)) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn3aR hK.le) (sqrt_nonneg _)
    _ ≤ K*(3*(a : ℝ))/sqrt (log (a : ℝ)) := div_le_div_of_nonneg_left (by positivity) hrootA hrootle
    _ = (3*K)*(a : ℝ)/sqrt (log (a : ℝ)) := by ring
    _ ≤ _ := hbound'
    _ ≤ _ := hCH
end HadwigerRamsey
