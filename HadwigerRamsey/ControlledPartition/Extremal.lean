import HadwigerRamsey.ControlledPartition.Parameters
import HadwigerRamsey.ControlledPartition.Connectivity
import HadwigerRamsey.ControlledPartition.Preliminary

open Finset
open scoped Classical

namespace HadwigerRamsey.ControlledPartition

def Admissible {n : ℕ} (G : SimpleGraph (Fin n)) (ε δ : ℝ)
    (P : Decomposition n) : Prop :=
  (P.X.card : ℝ) ≤ ε^2*n ∧
  DegenerateOn G P.Y (3*ε*n) ∧
  (∀ S ∈ P.parts, RealConnected G S ((P.parts.card.factorial : ℝ)*δ*n)) ∧
  (∀ S ∈ P.parts, 2*ε*n ≤ (S.card : ℝ))

def NeighborBound {n : ℕ} (G : SimpleGraph (Fin n)) (η : ℝ)
    (P : Decomposition n) : Prop :=
  ∀ v ∈ P.Y, ((nbr G P.core v).card : ℝ) ≤ η*n

theorem admissible_exists {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hεsmall : ε ≤ 1/3) :
    ∃ P : Decomposition n, Admissible G ε (cutoff ε η) P := by
  obtain ⟨P,hX,hY,hconn,hsize,hk⟩ := preliminary G hn ε hε hεsmall
  refine ⟨P,hX,hY,?_,hsize⟩
  intro S hS
  exact (hconn S hS).mono (by
    have hh := mul_le_mul_of_nonneg_right (cutoff_bounds hε hη hk).1
      (show (0 : ℝ) ≤ n by positivity)
    simpa only [mul_assoc] using hh)


/-- Minimize the remainder, then add any vertex violating its neighbour bound. -/
theorem prepared_exists {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hεsmall : ε ≤ 1/3) :
    ∃ P : Decomposition n,
      Admissible G ε (cutoff ε η) P ∧ NeighborBound G η P := by
  classical
  let C : Set (Decomposition n) := {P | Admissible G ε (cutoff ε η) P}
  obtain ⟨P,hP,hmin⟩ := C.exists_min_image (fun P => P.Y.card)
    (Set.toFinite C) (admissible_exists G hn hε hη hεsmall)
  have hp : Admissible G ε (cutoff ε η) P := hP
  refine ⟨P,hp,?_⟩
  intro v hv
  by_contra! hbad
  have hk := (parts_bound hn hε P hp.2.2.2).2
  obtain ⟨S,hS,hdeg⟩ := exists_many_neighbors G P hε hη.le hk v hbad
  have hvS : v ∉ S := fun h => disjoint_left.mp (P.disjoint_Y S hS) h hv
  let Q := P.absorb hS hv
  have hcard : Q.parts.card = P.parts.card := P.absorb_card hS hv
  have hQ : Admissible G ε (cutoff ε η) Q := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [Q, Decomposition.absorb_X] using hp.1
    · simpa only [Q, Decomposition.absorb_Y] using
        (hp.2.1.mono (erase_subset _ _) le_rfl)
    · intro T hT
      rw [hcard]
      have ht : T = insert v S ∨ T ∈ P.parts.erase S := by
        simpa only [Q, Decomposition.absorb_parts,mem_insert] using hT
      rcases ht with rfl | hT
      · apply (hp.2.2.1 S hS).add_vertex hvS
        have hh := mul_le_mul_of_nonneg_right (cutoff_bounds hε hη hk).2
          (show (0 : ℝ) ≤ n by positivity)
        nlinarith only [hh,hdeg]
      · exact hp.2.2.1 T (mem_erase.mp hT).2
    · intro T hT
      have ht : T = insert v S ∨ T ∈ P.parts.erase S := by
        simpa only [Q, Decomposition.absorb_parts,mem_insert] using hT
      rcases ht with rfl | hT
      · exact (hp.2.2.2 S hS).trans (by exact_mod_cast card_le_card (subset_insert v S))
      · exact hp.2.2.2 T (mem_erase.mp hT).2
  have hh := hmin Q hQ
  have hY : Q.Y.card + 1 = P.Y.card := by
    simp only [Q, Decomposition.absorb_Y]
    exact card_erase_add_one hv
  omega

/-- Minimize the number of robust pieces after enforcing the remainder bound. -/
theorem extremal_partition {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hεsmall : ε ≤ 1/3) :
    ∃ P : Decomposition n,
      Admissible G ε (cutoff ε η) P ∧ NeighborBound G η P ∧
      ∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T →
        ¬RealConnected G (S ∪ T) (((P.parts.card-1).factorial : ℝ)*cutoff ε η*n) := by
  classical
  let C : Set (Decomposition n) :=
    {P | Admissible G ε (cutoff ε η) P ∧ NeighborBound G η P}
  obtain ⟨P,hP,hmin⟩ := C.exists_min_image (fun P => P.parts.card)
    (Set.toFinite C) (prepared_exists G hn hε hη hεsmall)
  have hp : Admissible G ε (cutoff ε η) P ∧ NeighborBound G η P := hP
  refine ⟨P,hp.1,hp.2,?_⟩
  intro S hS T hT hST hmerge
  let Q := P.merge hS hT hST
  have hcard : Q.parts.card + 1 = P.parts.card := P.merge_card hS hT hST
  have hqprev : Q.parts.card = P.parts.card-1 := by omega
  have hscale : (Q.parts.card.factorial : ℝ)*cutoff ε η*n ≤
      (P.parts.card.factorial : ℝ)*cutoff ε η*n := by
    have hf : (Q.parts.card.factorial : ℝ) ≤ (P.parts.card.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : Q.parts.card ≤ P.parts.card)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hf (cutoff_pos hε hη).le) (Nat.cast_nonneg _)
  have hQ : Admissible G ε (cutoff ε η) Q ∧ NeighborBound G η Q := by
    constructor
    · refine ⟨?_,?_,?_,?_⟩
      · simpa only [Q,Decomposition.merge_X] using hp.1.1
      · simpa only [Q,Decomposition.merge_Y] using hp.1.2.1
      · intro U hU
        have hu : U ∈ P.parts \ {S,T} ∨ U = S ∪ T := by
          simpa only [Q,Decomposition.merge_parts,mem_union,mem_singleton] using hU
        rcases hu with hU | rfl
        · exact (hp.1.2.2.1 U (mem_sdiff.mp hU).1).mono hscale
        · simpa only [hqprev] using hmerge
      · intro U hU
        have hu : U ∈ P.parts \ {S,T} ∨ U = S ∪ T := by
          simpa only [Q,Decomposition.merge_parts,mem_union,mem_singleton] using hU
        rcases hu with hU | rfl
        · exact hp.1.2.2.2 U (mem_sdiff.mp hU).1
        · exact (hp.1.2.2.2 S hS).trans (by
            exact_mod_cast card_le_card (subset_union_left : S ⊆ S ∪ T))
    · simpa only [NeighborBound,Q,Decomposition.merge_Y,Decomposition.merge_core]
        using hp.2
  have hh := hmin Q hQ
  omega

end HadwigerRamsey.ControlledPartition
