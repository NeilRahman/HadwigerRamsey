import HadwigerRamsey.Graph

namespace HadwigerRamsey.ThomasonUpper

/-- Adding vertices each adjacent to a connected core preserves connectedness.
This is the last connectivity step of the appendix. -/
theorem connected_of_dominated_core {V : Type*} {G : SimpleGraph V}
    {W K : Set V} (hK : (G.induce K).Connected)
    (hdom : ∀ v ∈ W, ∃ u ∈ K, G.Adj v u) :
    (G.induce (W ∪ K)).Connected := by
  obtain ⟨u, hu⟩ := hK.nonempty
  apply G.induce_connected_of_patches u (Or.inr hu)
  intro v hv
  rcases hv with hv | hv
  · obtain ⟨w, hw, hvw⟩ := hdom v hv
    have hpair := G.induce_pair_connected_of_adj hvw
    have hconn := G.induce_union_connected hK hpair ⟨w, hw, by simp⟩
    refine ⟨K ∪ {v, w}, ?_, Or.inl hu, Or.inr (by simp), hconn _ _⟩
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact Or.inl hv
      · exact Or.inr (Set.mem_singleton_iff.mp hx ▸ hw)
  · exact ⟨K, Set.subset_union_right, hu, hv, hK _ _⟩

/-- A complete family becomes a clique minor after adjoining pairwise disjoint
connected cores that dominate its members. -/
theorem cliqueMinor_of_complete_dominated {V : Type*} {G : SimpleGraph V}
    {m : ℕ} (W K : Fin m → Set V)
    (hK : ∀ a, (G.induce (K a)).Connected)
    (hdom : ∀ a v, v ∈ W a → ∃ u ∈ K a, G.Adj v u)
    (hdisj : ∀ a b, a ≠ b → Disjoint (W a ∪ K a) (W b ∪ K b))
    (hcomplete : ∀ a b, a ≠ b → ∃ u ∈ W a, ∃ v ∈ W b, G.Adj u v) :
    HasCliqueMinor G m := by
  refine ⟨fun a => W a ∪ K a,
    fun a => connected_of_dominated_core (hK a) (hdom a), hdisj, ?_⟩
  intro a b hab
  obtain ⟨u, hu, v, hv, huv⟩ := hcomplete a b hab
  exact ⟨u, Or.inl hu, v, Or.inl hv, huv⟩

/-- Connected enlargements of a complete family also give a clique minor.
The sets may lie in a larger graph than the one producing completeness. -/
theorem cliqueMinor_of_complete_enlargements {V : Type*} {G : SimpleGraph V}
    {m : ℕ} (W B : Fin m → Set V)
    (hWB : ∀ a, W a ⊆ B a)
    (hconn : ∀ a, (G.induce (B a)).Connected)
    (hdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hcomplete : ∀ a b, a ≠ b → ∃ u ∈ W a, ∃ v ∈ W b, G.Adj u v) :
    HasCliqueMinor G m := by
  refine ⟨B, hconn, hdisj, ?_⟩
  intro a b hab
  obtain ⟨u, hu, v, hv, huv⟩ := hcomplete a b hab
  exact ⟨u, hWB a hu, v, hWB b hv, huv⟩

/-- A nonempty family of walks with a common starting vertex has connected
union. This turns disjointly allocated connecting paths into a connected core. -/
theorem connected_walk_union {V J : Type*} [Nonempty J] {G : SimpleGraph V}
    {u : V} (v : J → V) (P : ∀ j, G.Walk u (v j)) :
    (G.induce {x | ∃ j, x ∈ (P j).support}).Connected := by
  let j₀ : J := Classical.choice inferInstance
  have hu : u ∈ ({x | ∃ j, x ∈ (P j).support} : Set V) :=
    ⟨j₀, (P j₀).start_mem_support⟩
  apply G.induce_connected_of_patches u hu
  intro x hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨{y | y ∈ (P j).support}, fun y hy => ⟨j, hy⟩,
    (P j).start_mem_support, hj, (P j).connected_induce_support _ _⟩

end HadwigerRamsey.ThomasonUpper
