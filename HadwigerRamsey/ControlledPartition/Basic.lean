import HadwigerRamsey.ControlledPartition.Definitions

open Finset
open scoped Classical
namespace HadwigerRamsey.ControlledPartition

@[simp] theorem mem_nbr {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v w : Fin n) :
    w ∈ nbr G S v ↔ w ∈ S ∧ G.Adj v w := by
  classical
  simp [nbr]

theorem nbr_mono {n : ℕ} (G : SimpleGraph (Fin n))
    {S T : Finset (Fin n)} (h : S ⊆ T) (v : Fin n) :
    nbr G S v ⊆ nbr G T v := by
  intro w hw
  exact (mem_nbr _ _ _ _).mpr ⟨h ((mem_nbr _ _ _ _).mp hw).1,
    ((mem_nbr _ _ _ _).mp hw).2⟩

theorem nbr_card_lt {n : ℕ} (G : SimpleGraph (Fin n))
    {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) :
    (nbr G S v).card < S.card := by
  classical
  apply card_lt_card
  refine (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
  · intro w hw
    exact ((mem_nbr _ _ _ _).mp hw).1
  · intro h
    have hh : v ∈ nbr G S v := h.symm ▸ hv
    exact G.irrefl ((mem_nbr _ _ _ _).mp hh).2

theorem nbr_loss {n : ℕ} (G : SimpleGraph (Fin n))
    {S A B Z : Finset (Fin n)} (hcover : A ∪ B = S \ Z)
    (hcross : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v) {v : Fin n} (hv : v ∈ A) :
    (nbr G S v).card ≤ (nbr G A v).card + Z.card := by
  classical
  calc
    _ ≤ (nbr G A v ∪ Z).card := card_le_card (by
      intro w hw
      obtain ⟨hwS, hadj⟩ := (mem_nbr _ _ _ _).mp hw
      by_cases hwZ : w ∈ Z
      · exact mem_union_right _ hwZ
      · have hwAB : w ∈ A ∪ B := hcover.symm ▸ mem_sdiff.mpr ⟨hwS,hwZ⟩
        rcases mem_union.mp hwAB with hwA | hwB
        · exact mem_union_left _ ((mem_nbr _ _ _ _).mpr ⟨hwA,hadj⟩)
        · exact (hcross v hv w hwB hadj).elim)
    _ ≤ _ := card_union_le _ _

theorem DegenerateOn.mono {n : ℕ} {G : SimpleGraph (Fin n)}
    {Y Z : Finset (Fin n)} {d e : ℝ} (h : DegenerateOn G Y d)
    (hZY : Z ⊆ Y) (hde : d ≤ e) : DegenerateOn G Z e := by
  intro S hS hn
  obtain ⟨v,hv,hd⟩ := h S (hS.trans hZY) hn
  exact ⟨v,hv,hd.trans hde⟩

theorem DegenerateOn.of_large {n : ℕ} (G : SimpleGraph (Fin n))
    (Y : Finset (Fin n)) {d : ℝ} (hd : (n : ℝ) ≤ d) : DegenerateOn G Y d := by
  intro S _ hS
  obtain ⟨v,hv⟩ := hS
  refine ⟨v,hv,?_⟩
  have hh : (nbr G S v).card ≤ n := by simpa using (nbr G S v).card_le_univ
  exact (show ((nbr G S v).card : ℝ) ≤ n by exact_mod_cast hh).trans hd

end HadwigerRamsey.ControlledPartition
