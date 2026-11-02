import Mathlib

open Finset
open scoped Classical

namespace HadwigerRamsey.ControlledPartition

noncomputable def nbr {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  S.filter (G.Adj v)

/-- Real thresholds for the usual vertex-deletion definition of connectivity. -/
def RealConnected {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (t : ℝ) : Prop :=
  t ≤ (S.card : ℝ) - 1 ∧
  ∀ Z : Finset (Fin n), Z ⊆ S → (Z.card : ℝ) < t →
    (G.induce (↑(S \ Z) : Set (Fin n))).Connected

/-- Every nonempty induced subgraph has a vertex of degree at most the threshold. -/
def DegenerateOn {n : ℕ} (G : SimpleGraph (Fin n))
    (Y : Finset (Fin n)) (d : ℝ) : Prop :=
  ∀ S ⊆ Y, S.Nonempty → ∃ v ∈ S, (nbr G S v).card ≤ d

/-- The connected pieces together with the two exceptional classes form a partition.
The distinguished classes may be empty; the connected pieces are nonempty. -/
structure Decomposition (n : ℕ) where
  parts : Finset (Finset (Fin n))
  X : Finset (Fin n)
  Y : Finset (Fin n)
  nonempty : ∀ S ∈ parts, S.Nonempty
  pairwise : (parts : Set (Finset (Fin n))).PairwiseDisjoint id
  disjoint_X : ∀ S ∈ parts, Disjoint S X
  disjoint_Y : ∀ S ∈ parts, Disjoint S Y
  disjoint_XY : Disjoint X Y
  cover : parts.biUnion id ∪ X ∪ Y = univ

noncomputable def Decomposition.core {n : ℕ} (P : Decomposition n) :=
  P.parts.biUnion id

def Controlled {n : ℕ} (G : SimpleGraph (Fin n))
    (ε η δ : ℝ) (P : Decomposition n) : Prop :=
  (P.X.card : ℝ) ≤ ε * n ∧
  (∀ S ∈ P.parts, RealConnected G S (δ * n)) ∧
  DegenerateOn G P.Y (3 * ε * n) ∧
  (∀ v ∈ P.Y, ((nbr G P.core v).card : ℝ) ≤ η * n) ∧
  (∀ S ∈ P.parts, ε * n ≤ (S.card : ℝ)) ∧
  (∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T →
    ∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v)

end HadwigerRamsey.ControlledPartition
