import HadwigerRamsey.ThomasonUpper.BlockMaxProducts

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- The eligible blocks are all blocks except the final one in each class. -/
def eligibleBlocks {k : ℕ} (ell : Fin k → ℕ) : Finset (Σ i, Fin (ell i)) :=
  univ.sigma (fun i => univ.filter (fun a : Fin (ell i) => a.val+1 < ell i))

theorem mem_eligibleBlocks {k : ℕ} (ell : Fin k → ℕ) (b : Σ i, Fin (ell i)) :
    b ∈ eligibleBlocks ell ↔ b.2.val+1 < ell b.1 := by
  simp [eligibleBlocks]

/-- Exactly k final blocks are omitted from eligibility. -/
theorem eligibleBlocks_card {k : ℕ} (ell : Fin k → ℕ) (hell : ∀ i, 1 ≤ ell i) :
    (eligibleBlocks ell).card+k = ∑ i, ell i := by
  have hc : ∀ i, (univ.filter (fun a : Fin (ell i) => a.val+1 < ell i)).card = ell i-1 := by
    intro i
    let last : Fin (ell i) := ⟨ell i-1,by have := hell i; omega⟩
    have he : univ.filter (fun a : Fin (ell i) => a.val+1 < ell i) = univ.erase last := by
      ext a
      simp only [mem_filter,mem_univ,true_and,mem_erase,and_true,ne_eq,Fin.ext_iff,last]
      omega
    rw [he,card_erase_of_mem (mem_univ last),card_univ,Fintype.card_fin]
  rw [eligibleBlocks,card_sigma]
  simp_rw [hc]
  have hh : ∀ i, ell i-1+1 = ell i := fun i => by have := hell i; omega
  have he : (∑ i : Fin k, (ell i-1+1)) = ∑ i, ell i := sum_congr rfl (fun i _ => hh i)
  simpa only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id] using he

/-- Acceptability gives ell-m <= k+phi*ell for the retained eligible
blocks, including the exact loss of one final block per class. -/
theorem acceptable_missing_blocks {k L : ℕ} (ell : Fin k → ℕ)
    (hell : ∀ i, 1 ≤ ell i) (hsum : ∑ i, ell i = L)
    (rejected : Finset (Σ i, Fin (ell i))) {phi : ℝ}
    (haccept : (((eligibleBlocks ell) ∩ rejected).card : ℝ) ≤ phi*L) :
    (L : ℝ)-(((eligibleBlocks ell) \ rejected).card : ℝ) ≤ k+phi*L := by
  have hc := eligibleBlocks_card ell hell
  rw [hsum] at hc
  have hd := card_sdiff_add_card_inter (eligibleBlocks ell) rejected
  have hcR : ((eligibleBlocks ell).card : ℝ)+k = L := by exact_mod_cast hc
  have hdR : (((eligibleBlocks ell) \ rejected).card : ℝ)+
      (((eligibleBlocks ell) ∩ rejected).card : ℝ) = (eligibleBlocks ell).card := by exact_mod_cast hd
  linarith

/-- In the second-part estimate, unused block factors are at most one;
nonrejected factors cost at most 2*omega times theta to the ell-th power.
The constant is padded from the selected-block count to ell. -/
theorem selected_block_product_bound {I : Type*} [Fintype I]
    (M : Finset I) (z theta : I → ℝ) {s L : ℕ} (hs : 2 ≤ s)
    {omega : ℝ} (homega : 1 ≤ omega) (hcard : M.card ≤ L)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) (htheta : ∀ i ∈ M, 0 ≤ theta i)
    (hselected : ∀ i ∈ M, z i ≤ omega*(s : ℝ)*(theta i)^L/((s : ℝ)-1)) :
    (∏ i, z i) ≤ (2*omega)^L * ∏ i ∈ M, (theta i)^L := by
  classical
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : 0 < (s : ℝ)-1 := by linarith
  have hpM : 0 ≤ ∏ i ∈ M, z i := prod_nonneg (fun i _ => (hz i).1)
  have hpC : (∏ i ∈ univ \ M, z i) ≤ 1 := prod_le_one
    (fun i _ => (hz i).1) (fun i _ => (hz i).2)
  have hdrop : (∏ i, z i) ≤ ∏ i ∈ M, z i := by
    rw [← prod_sdiff (subset_univ M) (f := z)]
    nlinarith
  have hper : ∀ i ∈ M, z i ≤ (2*omega)*(theta i)^L := by
    intro i hi
    apply (hselected i hi).trans
    apply (div_le_iff₀ hspos).mpr
    have hc : 0 ≤ omega*(theta i)^L := mul_nonneg (by linarith) (pow_nonneg (htheta i hi) _)
    have hh := mul_nonneg hc (show 0 ≤ (s : ℝ)-2 by linarith)
    nlinarith
  calc
    _ ≤ ∏ i ∈ M, z i := hdrop
    _ ≤ ∏ i ∈ M, (2*omega)*(theta i)^L := prod_le_prod
      (fun i _ => (hz i).1) hper
    _ = (2*omega)^M.card * ∏ i ∈ M, (theta i)^L := by rw [prod_mul_distrib,prod_const]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith : 1 ≤ 2*omega) hcard)
      (prod_nonneg (fun i hi => pow_nonneg (htheta i hi) _))

/-- Acceptability changes the omitted-block exponent to the exact
k+phi*ell exponent in the definition of P. -/
theorem acceptable_tau_factor {t phi : ℝ} {L k : ℕ} {m : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hmissing : (L : ℝ)-m ≤ k+phi*L) :
    t^(-((L : ℝ)*((L : ℝ)-m))) ≤ t^(-((L : ℝ)*(k+phi*L))) := by
  apply rpow_le_rpow_of_exponent_ge ht ht1
  nlinarith [show (0 : ℝ) ≤ L by positivity]

/-- Combining the selected factors, the sorted-maxima bound, and
acceptability yields the exact expression P of A.1. The graph-dependent
inputs to this numerical step are provided by the sampling and sorting
lemmas; their full defect-count assembly is separate. -/
theorem acceptable_pair_product_bound {I : Type*} [Fintype I]
    (M : Finset I) (z theta : I → ℝ) {s L k : ℕ} (hs : 2 ≤ s)
    {omega t phi Q : ℝ} (homega : 1 ≤ omega) (ht : 0 < t) (ht1 : t ≤ 1)
    (hQ : 0 ≤ Q) (hcard : M.card ≤ L)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) (htheta : ∀ i ∈ M, 0 ≤ theta i)
    (hselected : ∀ i ∈ M, z i ≤ omega*(s : ℝ)*(theta i)^L/((s : ℝ)-1))
    (hmax : (∏ i ∈ M, (theta i)^L) ≤ Q*t^(-((L : ℝ)*((L : ℝ)-M.card))))
    (hmissing : (L : ℝ)-M.card ≤ k+phi*L) :
    (∏ i, z i) ≤ (2*omega)^L * t^(-((L : ℝ)*(k+phi*L))) * Q := by
  have hc : 0 ≤ (2*omega)^L := pow_nonneg (by linarith) _
  have htau := acceptable_tau_factor ht ht1 hmissing
  calc
    _ ≤ (2*omega)^L * ∏ i ∈ M, (theta i)^L :=
      selected_block_product_bound M z theta hs homega hcard hz htheta hselected
    _ ≤ (2*omega)^L * (Q*t^(-((L : ℝ)*((L : ℝ)-M.card)))) :=
      mul_le_mul_of_nonneg_left hmax hc
    _ ≤ (2*omega)^L * (Q*t^(-((L : ℝ)*(k+phi*L)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htau hQ) hc
    _ = _ := by ring

end HadwigerRamsey.ThomasonUpper
