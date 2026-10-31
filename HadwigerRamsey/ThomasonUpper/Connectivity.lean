import HadwigerRamsey.ThomasonUpper.Definitions

open Finset

namespace HadwigerRamsey.ThomasonUpper

theorem VertexConnectedAtLeast.mono {n : ℕ} {G : SimpleGraph (Fin n)}
    {d e : ℕ} (h : VertexConnectedAtLeast G d) (he : e ≤ d) :
    VertexConnectedAtLeast G e :=
  ⟨he.trans_lt h.1, fun Z hZ => h.2 Z (hZ.trans_le he)⟩

theorem vertexConnectivity_lt {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    vertexConnectivity G < n := by
  classical
  by_cases h : vertexConnectivity G = 0
  · simpa [h] using hn
  · exact (Nat.findGreatest_of_ne_zero (P := VertexConnectedAtLeast G) rfl h).1

/-- The defined maximum has exactly the usual deletion characterization. -/
theorem vertexConnectedAtLeast_iff {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (d : ℕ) :
    VertexConnectedAtLeast G d ↔ d ≤ vertexConnectivity G := by
  classical
  have hz : VertexConnectedAtLeast G 0 := ⟨hn, by intro Z hZ; omega⟩
  constructor
  · intro h
    exact Nat.le_findGreatest h.1.le h
  · intro hd
    have hm : VertexConnectedAtLeast G (vertexConnectivity G) :=
      Nat.findGreatest_spec (Nat.zero_le n) hz
    exact hm.mono hd

/-- Removing all neighbors of v isolates v. Vertex connectivity cannot
exceed its degree; this supplies the density lower bound used in the appendix. -/
theorem VertexConnectedAtLeast.le_degree {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {d : ℕ} (h : VertexConnectedAtLeast G d)
    (v : Fin n) : d ≤ G.degree v := by
  classical
  by_contra! hsmall
  let Z := G.neighborFinset v
  have hvZ : v ∉ Z := by simp [Z]
  have hZ : Z.card < d := by simpa [Z] using hsmall
  have hcard : (insert v Z).card < (univ : Finset (Fin n)).card := by
    rw [card_insert_of_notMem hvZ, card_univ, Fintype.card_fin]
    have : Z.card + 1 ≤ d := hZ
    have := h.1
    omega
  obtain ⟨w, _, hw⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hwZ : w ∉ Z := fun hwZ => hw (mem_insert_of_mem hwZ)
  have hwv : w ≠ v := fun hwv => hw (by simp [hwv])
  obtain ⟨p⟩ := h.2 Z hZ ⟨v, hvZ⟩ ⟨w, hwZ⟩
  cases p with
  | nil => exact hwv rfl
  | @cons _ b _ hab _ =>
    exact b.property (by simpa [Z] using hab)

theorem vertexConnectivity_le_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) : vertexConnectivity G ≤ G.degree v := by
  exact ((vertexConnectedAtLeast_iff (Nat.pos_of_ne_zero (by
    intro hn; subst n; exact Fin.elim0 v)) G _).2 le_rfl).le_degree v

/-- The large-epsilon case in the manuscript is vacuous. -/
theorem connectivity_excludes_large_epsilon {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) {ε : ℝ}
    (hconn : ε * n ≤ (vertexConnectivity G : ℝ)) : ε < 1 := by
  have hκ : (vertexConnectivity G : ℝ) < n := by
    exact_mod_cast vertexConnectivity_lt hn G
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

end HadwigerRamsey.ThomasonUpper
