import HadwigerRamsey.Blocks

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey
namespace ThomasonUpper

/-- The fibers of the vertex-to-class map encode the manuscript's partition. -/
def classVertices {n k : ℕ} (τ : Fin n → Fin k) (i : Fin k) : Finset (Fin n) :=
  univ.filter fun v => τ v = i

/-- Ordinary undirected edge density inside one class. Division by zero is
irrelevant once the theorem's size threshold makes every class have size two. -/
noncomputable def internalDensity {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) : ℝ := by
  classical
  exact ((G.induce (S : Set V)).edgeFinset.card : ℝ) / (S.card.choose 2 : ℝ)

/-- Off-diagonal densities use Mathlib's density; diagonal densities use
the number of unordered edges divided by the number of unordered pairs. -/
noncomputable def blockDensity {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) : ℝ := by
  classical
  exact if i = j then internalDensity G (classVertices τ i)
    else (G.edgeDensity (classVertices τ i) (classVertices τ j) : ℝ)

/-- The density cap in Theorem 1.5. -/
noncomputable def cappedDensity {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (ε : ℝ) (i j : Fin k) : ℝ :=
  min (blockDensity G τ i j) (1 - ε)

/-- The exact ordered double sum under the square root in Theorem 1.5. -/
noncomputable def cappedLambda {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (ε : ℝ) : ℝ :=
  blockLambda τ (cappedDensity G τ ε)

/-- The usual cut characterization of vertex connectivity at least `d`.
The order bound gives a complete graph on `n` vertices connectivity `n-1`. -/
def VertexConnectedAtLeast {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  d < n ∧ ∀ Z : Finset (Fin n), Z.card < d →
    (G.induce ((Z : Set (Fin n))ᶜ)).Connected

/-- Vertex connectivity, with value zero also for the empty graph. -/
noncomputable def vertexConnectivity {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Nat.findGreatest (VertexConnectedAtLeast G) n

/-- The precise statement of Theorem 1.5. It is proved by
`HadwigerRamsey.thomasonupper` in the endpoint module. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ G : SimpleGraph (Fin n), (ε * n ≤ (vertexConnectivity G : ℝ)) →
    ∀ k : ℕ, ∀ τ : Fin n → Fin k,
      (∀ i, ε ≤ classMass τ i) →
      (n : ℝ) / sqrt (log n) * (sqrt (cappedLambda G τ ε) - ε) ≤
        (hadwigerNumber G : ℝ)

end ThomasonUpper
end HadwigerRamsey
