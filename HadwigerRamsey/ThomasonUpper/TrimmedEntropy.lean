import HadwigerRamsey.ThomasonUpper.Restriction
import HadwigerRamsey.ThomasonUpper.Regularization

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

theorem trimmed_classes_eq_survivors {n k : ℕ} (classes : Fin n → Fin k)
    (X : Fin k → Finset (Fin n)) (hX : ∀ i, X i ⊆ classVertices classes i) (i : Fin k) :
    classVertices classes i \ (univ \ univ.biUnion X) = X i := by
  ext v
  constructor
  · intro hv
    have hc := (mem_filter.mp (mem_sdiff.mp hv).1).2
    have hU : v ∈ univ.biUnion X := by
      by_contra h
      exact (mem_sdiff.mp hv).2 (mem_sdiff.mpr ⟨mem_univ _,h⟩)
    obtain ⟨j,hj,hv⟩ := mem_biUnion.mp hU
    have he : j = i := ((mem_filter.mp (hX j hv)).2).symm.trans hc
    simpa only [he] using hv
  · intro hv
    refine mem_sdiff.mpr ⟨hX i hv,?_⟩
    intro hz
    exact (mem_sdiff.mp hz).2 (mem_biUnion.mpr ⟨i,mem_univ _,hv⟩)

/-- The regularized entropy of rounded weights after deletion is close
to the original graph entropy. All errors are explicit and uniform in k. -/
theorem rounded_deleted_entropy_error {n k L : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (Z : Finset (Fin n)) (m : Fin k → ℕ)
    {a delta tau : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hdelta : 0 ≤ delta) (hdeltasmall : delta < a/2)
    (hn : 4 ≤ a*n) (hZ : (Z.card : ℝ) ≤ delta*n)
    (hsize : ∀ i, a*n ≤ (classVertices classes i).card)
    (hq : ∀ i j, a ≤ 1-blockDensity G classes i j)
    (hsmall : 8*delta/a ≤ a/2) (hL : 0 < L) (hsum : ∑ i, m i = L)
    (hround : ∀ i, |(m i : ℝ)/L-classMass classes i| ≤ 1/(L : ℝ)) (htau : 0 ≤ tau) :
    |regularizedLambda (fun i => (m i : ℝ)/L)
        (fun i j => 1-deletedBlockDensity G classes Z i j) tau -
      blockLambda classes (blockDensity G classes)| ≤
      tau/a + 16*delta/a^2 + 2*log (2/a)/(a*L) := by
  have hnR : (0 : ℝ) < n := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnN : 0 < n := by exact_mod_cast hnR
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hb := vertex_deletion_bounds G classes Z ha ha1 hdelta hdeltasmall hn hZ hsize
  have hqdel : ∀ i j, a/2 ≤ 1-deletedBlockDensity G classes Z i j := by
    intro i j
    have hh := (abs_le.mp (hb.2.2.2 i j)).2
    linarith [hq i j]
  have hk : (k : ℝ)*a ≤ 1 := by
    calc
      _ = ∑ _i : Fin k, a := by simp
      _ ≤ ∑ i, classMass classes i := sum_le_sum (fun i _ => (le_div_iff₀ hnR).mpr (hsize i))
      _ = 1 := sum_classMass hnN classes
  have hdiff : (∑ i, |classMass classes i-(m i : ℝ)/L|) ≤ 1/(a*L) := by
    calc
      _ ≤ ∑ _i : Fin k, 1/(L : ℝ) := sum_le_sum (fun i _ => by simpa only [abs_sub_comm] using hround i)
      _ = (k : ℝ)/(L : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        have hk' : (k : ℝ) ≤ 1/a := (le_div_iff₀ ha).mpr hk
        calc
          _ ≤ (1/a)/(L : ℝ) := div_le_div_of_nonneg_right hk' hLR.le
          _ = _ := by ring
  have hsumBeta : ∑ i, (m i : ℝ)/L = 1 := by
    rw [← sum_div,← Nat.cast_sum,hsum,div_self hLR.ne']
  have hstab := regularizedLambda_stability (classMass classes) (fun i => (m i : ℝ)/L)
    (fun i j => 1-blockDensity G classes i j)
    (fun i j => 1-deletedBlockDensity G classes Z i j)
    (a := a/2) (d := 8*delta/a) (by linarith) (by linarith) htau
    (classMass_nonneg classes) (fun _ => by positivity) (sum_classMass hnN classes) hsumBeta
    (fun i j => by linarith [hq i j]) hqdel
    (fun i j => by
      have he : (1-blockDensity G classes i j)-(1-deletedBlockDensity G classes Z i j) =
          deletedBlockDensity G classes Z i j-blockDensity G classes i j := by ring
      rw [he]
      exact hb.2.2.2 i j)
  have hid : (1 : ℝ)/(a/2) = 2/a := by field_simp
  have he : (8*delta/a)/(a/2) = 16*delta/a^2 := by field_simp; ring
  rw [hid,he] at hstab
  have hlog : 0 ≤ log (2/a) := log_nonneg ((le_div_iff₀ ha).mpr (by linarith))
  have hstab' := hstab.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 2*log (2/a))))
  have hreg := regularizedLambda_error (classMass classes)
    (fun i j => 1-blockDensity G classes i j) ha htau (classMass_nonneg classes)
    (sum_classMass hnN classes) (fun i j => ⟨hq i j,by linarith [blockDensity_nonneg G classes i j]⟩)
  have hregabs : |regularizedLambda (classMass classes)
      (fun i j => 1-blockDensity G classes i j) tau - blockLambda classes (blockDensity G classes)| ≤ tau/a := by
    change 0 ≤ blockLambda classes (blockDensity G classes) - _ ∧ _ at hreg
    rw [abs_sub_comm,abs_of_nonneg hreg.1]
    exact hreg.2
  have htri := (abs_sub_le
    (regularizedLambda (fun i => (m i : ℝ)/L) (fun i j => 1-deletedBlockDensity G classes Z i j) tau)
    (regularizedLambda (classMass classes) (fun i j => 1-blockDensity G classes i j) tau)
    (blockLambda classes (blockDensity G classes))).trans
      (add_le_add (by simpa only [abs_sub_comm] using hstab') hregabs)
  calc
    _ ≤ (16*delta/a^2 + 2*log (2/a)*(1/(a*L))) + tau/a := htri
    _ = _ := by ring

end HadwigerRamsey.ThomasonUpper
