import HadwigerRamsey.ThomasonUpper.ClassBlocks
import HadwigerRamsey.ThomasonUpper.UniformInstances
import HadwigerRamsey.ThomasonUpper.BlockAMGM
import HadwigerRamsey.ThomasonUpper.FiniteExpectations

open scoped BigOperators Classical ENNReal
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The arithmetic mean of the block nonneighbor proportions is bounded
by the regularized nonneighbor fraction of the whole class. -/
theorem nonneighbor_block_proportion_sum {n k s : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (ell : Fin k → ℕ) (hs : 0 < s)
    (hell : ∀ i, 1 ≤ ell i)
    (e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i)
    (hcard : ∀ i, (classVertices classes i).card = s*ell i)
    {t : ℝ} (ht : 0 ≤ t) (u : Fin n) (j : Fin k) :
    (∑ a, (((univ.filter (fun x : Fin s => Gᶜ.Adj u (e j (a,x)))).card : ℝ)/s)) ≤
      (ell j : ℝ)*min 1 (nonneighborFraction G classes j u+t) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hellR : (0 : ℝ) < ell j := by exact_mod_cast (by have := hell j; omega : 0 < ell j)
  have hcR : (0 : ℝ) < (classVertices classes j).card := by
    rw [hcard,Nat.cast_mul]
    positivity
  have hd : nonneighborFraction G classes j u ≤ 1 := by
    unfold nonneighborFraction
    apply (div_le_iff₀ hcR).mpr
    norm_cast
    simpa using (card_filter_le (classVertices classes j) (Gᶜ.Adj u))
  have heq : (∑ a, (((univ.filter (fun x : Fin s => Gᶜ.Adj u (e j (a,x)))).card : ℝ)/s)) =
      (ell j : ℝ)*nonneighborFraction G classes j u := by
    rw [← sum_div,← Nat.cast_sum, sum_block_filter_card (classVertices classes j) (e j) (Gᶜ.Adj u)]
    unfold nonneighborFraction
    rw [hcard,Nat.cast_mul]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left (le_min hd (by linarith)) hellR.le

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The random-part nonneighbor probability in A.1, with the original
class counts and the exact rho weight. -/
theorem random_part_nonneighbor_probability {n k s L : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (ell : Fin k → ℕ) (hs : 0 < s)
    (hell : ∀ i, 1 ≤ ell i) (hL : 0 < L)
    (e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i)
    (hcard : ∀ i, (classVertices classes i).card = s*ell i)
    {t : ℝ} (ht : 0 < t) (position : Fin s) (u : Fin n) :
    ((PMF.uniformOfFintype ((Σ i, Fin (ell i)) → Equiv.Perm (Fin s))).toOuterMeasure
      {p | blockPart (classBlockEnumeration classes ell e) p position ⊆
        univ.filter (Gᶜ.Adj u)}).toReal ≤ (nonneighborWeight G classes ell L t u)^L := by
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  let T : (Σ i, Fin (ell i)) → Finset (Fin s) :=
    fun b => univ.filter (fun x => Gᶜ.Adj u (classBlockEnumeration classes ell e (b,x)))
  have hevent : {p | blockPart (classBlockEnumeration classes ell e) p position ⊆
      univ.filter (Gᶜ.Adj u)} =
      {p | ∀ b, p b position ∈ T b} := by
    ext p
    simp only [blockPart_subset_iff,T,mem_filter,mem_univ,true_and]
  rw [hevent]
  rw [uniform_block_event_of_fintype _ position T,ENNReal.toReal_prod]
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,Fintype.card_fin]
  rw [Fintype.prod_sigma]
  apply multitype_block_product_le_weight ell hL
    (fun j => min 1 (nonneighborFraction G classes j u+t))
    (fun j a => (((T ⟨j,a⟩).card : ℝ)/s))
  · intro j
    have hd : 0 ≤ nonneighborFraction G classes j u := by unfold nonneighborFraction; positivity
    exact lt_min (by norm_num) (by linarith)
  · intro j a
    positivity
  · intro j
    calc
      _ = ∑ a, (((univ.filter (fun x : Fin s => Gᶜ.Adj u (e j (a,x)))).card : ℝ)/s) := by
        apply sum_congr rfl
        intro a ha
        apply congrArg (fun S : Finset (Fin s) => (S.card : ℝ)/s)
        ext x
        simp [T,classBlockEnumeration_apply]
        constructor
        · intro hx
          exact (mem_filter.mp hx).2
        · intro hx
          exact mem_filter.mpr ⟨mem_univ _,hx⟩
      _ ≤ _ := nonneighbor_block_proportion_sum G classes ell hs hell e hcard ht.le u j

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The event that a random part consists of nonneighbors of u. -/
noncomputable def blockNonneighborEvent {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] {s : ℕ} (G : SimpleGraph V) (e : I × Fin s ≃ V)
    (position : Fin s) (u : V) : Set (I → Equiv.Perm (Fin s)) :=
  {p | blockPart e p position ⊆ univ.filter (Gᶜ.Adj u)}

/-- Count the vertices of B whose nonneighbor event occurs. -/
noncomputable def blockNonneighborCount {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] {s : ℕ} (G : SimpleGraph V) (e : I × Fin s ≃ V)
    (position : Fin s) (B : Finset V) (p : I → Equiv.Perm (Fin s)) : ℕ :=
  (B.filter (fun u => p ∈ blockNonneighborEvent G e position u)).card

attribute [-instance] SimpleGraph.Compl.adjDecidable in
/-- The expected number of nonneighbors in any block B is at most
|B| times theta to the ell-th power, whenever rho is at most theta on B. -/
theorem expected_block_nonneighbors {n k s L : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (ell : Fin k → ℕ) (hs : 0 < s)
    (hell : ∀ i, 1 ≤ ell i) (hL : 0 < L) (hsum : ∑ i, ell i = L)
    (e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i)
    (hcard : ∀ i, (classVertices classes i).card = s*ell i)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (position : Fin s)
    (B : Finset (Fin n)) {theta : ℝ}
    (htheta : ∀ u ∈ B, nonneighborWeight G classes ell L t u ≤ theta) :
    (𝔼 p : ((Σ i, Fin (ell i)) → Equiv.Perm (Fin s)),
      (blockNonneighborCount G (classBlockEnumeration classes ell e) position B p : ℝ)) ≤
        (B.card : ℝ)*theta^L := by
  let A := fun u => blockNonneighborEvent G (classBlockEnumeration classes ell e) position u
  change (𝔼 p, ((B.filter (fun u => p ∈ A u)).card : ℝ)) ≤ _
  rw [expected_finset_event_count B A]
  calc
    _ ≤ ∑ u ∈ B, (nonneighborWeight G classes ell L t u)^L :=
      sum_le_sum (fun u _ => random_part_nonneighbor_probability G classes ell hs hell hL e hcard ht position u)
    _ ≤ ∑ _u ∈ B, theta^L := by
      apply sum_le_sum
      intro u hu
      apply pow_le_pow_left₀
      · exact ht.le.trans (rho_bounds G classes ell L hL hsum ht ht1 u).1
      · exact htheta u hu
    _ = _ := by simp

end HadwigerRamsey.ThomasonUpper
