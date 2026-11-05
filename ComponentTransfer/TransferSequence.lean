import ComponentTransfer.Ramsey

open scoped Classical Topology
open Filter Real
open HadwigerRamsey

namespace ComponentTransfer.Transfer

/-- Failure of the transfer bound produces arbitrarily large counterexamples
whose normalized Hadwiger numbers have one fixed strict upper bound. -/
theorem exists_bad_sequence {r : ℕ} {b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hnot : ¬ TransferBound r b) :
    ∃ B : ℝ, 0 ≤ B ∧ B < b ∧
      ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧ (∀ j, 2 ≤ N j) ∧
      ∃ G : ∀ j, Fin r → SimpleGraph (Fin (N j)),
        (∀ j, IsDecomposition (G j)) ∧
        ∀ j c, (hadwigerNumber (G j c) : ℝ) * sqrt (log (N j : ℝ))/(N j : ℝ) ≤ B := by
  have hex : ∃ ε : ℝ, 0 < ε ∧ ¬ (∀ᶠ n : ℕ in atTop,
      ∀ G : Fin r → SimpleGraph (Fin n), IsDecomposition G →
        ∃ c : Fin r, (b-ε)*n/sqrt (log (n : ℝ)) ≤ hadwigerNumber (G c)) := by
    simpa only [TransferBound, not_forall, Classical.not_imp, exists_prop] using hnot
  obtain ⟨ε,hε,hbad⟩ := hex
  have hεb : ε < b := by
    by_contra! hεb
    apply hbad
    apply Eventually.of_forall
    intro n G hG
    let c : Fin r := ⟨0,hr⟩
    refine ⟨c,?_⟩
    have hnonpos : (b-ε)*(n : ℝ)/sqrt (log (n : ℝ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
        (sqrt_nonneg _)
    exact hnonpos.trans (by positivity)
  have hfreq : ∃ᶠ n : ℕ in atTop, ∃ G : Fin r → SimpleGraph (Fin n), IsDecomposition G ∧
      ∀ c, (hadwigerNumber (G c) : ℝ) < (b-ε)*n/sqrt (log (n : ℝ)) := by
    simpa only [Filter.not_eventually, not_forall, Classical.not_imp, not_exists, not_le, exists_prop] using hbad
  have hchoose (j : ℕ) : ∃ n ≥ j+2,
      ∃ G : Fin r → SimpleGraph (Fin n), IsDecomposition G ∧
        ∀ c, (hadwigerNumber (G c) : ℝ) < (b-ε)*n/sqrt (log (n : ℝ)) := by
    obtain ⟨n,hn,hG⟩ := (hfreq.and_eventually (eventually_ge_atTop (j+2))).exists
    exact ⟨n,hG,hn⟩
  choose N hN G hG hupper using hchoose
  refine ⟨b-ε,by linarith,by linarith,N,?_,?_,G,hG,?_⟩
  · exact tendsto_atTop_mono (fun j => (by have := hN j; omega : j ≤ N j)) tendsto_id
  · intro j
    have := hN j
    omega
  · intro j c
    have hn : 2 ≤ N j := by have := hN j; omega
    have hnR : (0 : ℝ) < N j := by exact_mod_cast (show 0 < N j by omega)
    have hs : 0 < sqrt (log (N j : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast (show 1 < N j by omega)))
    have h := mul_lt_mul_of_pos_right (hupper j c) hs
    have he : ((b-ε)*(N j : ℝ)/sqrt (log (N j : ℝ))) * sqrt (log (N j : ℝ)) =
        (b-ε)*(N j : ℝ) := div_mul_cancel₀ _ hs.ne'
    rw [he] at h
    exact ((div_lt_iff₀ hnR).mpr h).le

end ComponentTransfer.Transfer
