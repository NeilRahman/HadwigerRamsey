import HadwigerRamsey.ControlledPartition.Extremal
import HadwigerRamsey.ControlledPartition.Pruning

open Finset
open scoped Classical

namespace HadwigerRamsey.ControlledPartition

theorem empty_controlled {n : ℕ} (G : SimpleGraph (Fin n))
    {ε η δ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hdeg : DegenerateOn G univ (3*ε*n)) :
    Controlled G ε η δ (Decomposition.empty n) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [Decomposition.empty,card_empty,Nat.cast_zero]
    positivity
  · simp [Decomposition.empty]
  · exact hdeg
  · intro v hv
    simp only [Decomposition.empty,Decomposition.core,biUnion_empty,nbr,filter_empty,
      card_empty,Nat.cast_zero]
    positivity
  · simp [Decomposition.empty]
  · simp [Decomposition.empty]

end ControlledPartition

open ControlledPartition

/-- Lemma 3.2: every finite graph admits a controlled partition, with a
positive connectivity parameter depending only on the two input errors. -/
theorem connectedsets (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ P : Decomposition n, Controlled G ε η δ P := by
  refine ⟨cutoff ε η,cutoff_pos hε hη,?_⟩
  intro n G
  by_cases hn : n = 0
  · refine ⟨Decomposition.empty n,empty_controlled G hε.le hη.le ?_⟩
    apply DegenerateOn.of_large
    simp [hn]
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  by_cases he : ε ≤ 1/3
  · obtain ⟨P,hP,hnb,hnomerge⟩ := extremal_partition G hn hε hη he
    exact prune G hn hε he (cutoff_pos hε hη) P hP.1 hP.2.2.2 hP.2.2.1 hP.2.1
      hnb hnomerge (cutoff_bounds hε hη (parts_bound hn hε P hP.2.2.2).2).1
  · refine ⟨Decomposition.empty n,empty_controlled G hε.le hη.le ?_⟩
    apply DegenerateOn.of_large
    have hh : 1 ≤ 3*ε := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)]

end HadwigerRamsey
