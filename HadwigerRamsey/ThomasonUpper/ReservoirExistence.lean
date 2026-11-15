import HadwigerRamsey.ThomasonUpper.ReservoirSampling
import HadwigerRamsey.ThomasonUpper.Menger
import HadwigerRamsey.ThomasonUpper.ReservoirAsymptotic

open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory Real

namespace HadwigerRamsey.ThomasonUpper

/-- The short-path step used to prove the reservoir result, Lemma A.4. -/
theorem short_paths_linear_connectivity {n : ℕ} (G : SimpleGraph (Fin n))
    {c : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hconn : c*n ≤ (vertexConnectivity G : ℝ)) {u v : Fin n} (huv : u ≠ v) :
    ∃ P : Finset (G.Path u v), c*n/2 ≤ (P.card : ℝ) ∧
      (∀ p ∈ P, p.val.length ≤ ⌈2/c⌉₊+1) ∧
      (P : Set (G.Path u v)).PairwiseDisjoint pathInterior := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < vertexConnectivity G := (mul_pos hc hnR).trans_le hconn
  have hk : 0 < vertexConnectivity G := by exact_mod_cast hkR
  obtain ⟨P, hcard, hlen, hd⟩ := short_paths_vertexConnectivity huv hk
  refine ⟨P, by linarith, ?_, hd⟩
  intro p hp
  have hr : 2*(n : ℝ)/(vertexConnectivity G : ℝ) ≤ 2/c :=
    (div_le_div_iff₀ hkR hc).mpr (by nlinarith)
  have hh := Nat.le_ceil (2/c)
  have hpR : (p.val.length : ℝ) ≤ (⌈2/c⌉₊+1 : ℕ) := by
    push_cast
    linarith [hlen p hp]
  exact_mod_cast hpR

/-- A stronger form of Lemma A.4 at a specified sampling rate.
The path count is at least `n*r^H` whenever `r ≤ c/4`. -/
def Reservoirs {n : ℕ} (G : SimpleGraph (Fin n)) (c r : ℝ) (H : ℕ)
    (C D : Finset (Fin n)) : Prop :=
  Disjoint C D ∧ (C.card : ℝ) ≤ 2*r*n ∧ (D.card : ℝ) ≤ 2*r*n ∧
    (∀ v, r*(G.degree v : ℝ)/2 ≤ ((D.filter (G.Adj v)).card : ℝ)) ∧
    ∀ u v, u ≠ v → ∃ Q : Finset (G.Path u v),
      c*n*r^(H-1)/4 ≤ (Q.card : ℝ) ∧
      (∀ p ∈ Q, p.val.length ≤ H ∧ pathInterior p ⊆ C) ∧
      (Q : Set (G.Path u v)).PairwiseDisjoint pathInterior

/-- A finite, stronger form of Lemma A.4. The numerical failure-probability condition is
subsequently discharged by the eventual logarithmic sampling rate. -/
theorem reservoirs_of_failure_lt_one {n : ℕ} (G : SimpleGraph (Fin n))
    {c r : ℝ} (hc : 0 < c) (hn : 0 < n) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hconn : c*n ≤ (vertexConnectivity G : ℝ))
    (hfailure : 2*exp (-2*r^2*n) + n*exp (-c*r^2*n/2) +
      (n : ℝ)^2*exp (-c*n*(r^(⌈2/c⌉₊))^2/4) < 1) :
    ∃ C D : Finset (Fin n), Reservoirs G c r (⌈2/c⌉₊+1) C D := by
  classical
  let H := ⌈2/c⌉₊+1
  let J := {e : Fin n × Fin n // e.1 ≠ e.2}
  have hpaths : ∀ e : J, ∃ P : Finset (G.Path e.val.1 e.val.2),
      c*n/2 ≤ (P.card : ℝ) ∧ (∀ p ∈ P, p.val.length ≤ H) ∧
      (P : Set (G.Path e.val.1 e.val.2)).PairwiseDisjoint pathInterior :=
    fun e => short_paths_linear_connectivity G hc hn hconn e.property
  choose P hPcard hPlen hPdisj using hpaths
  let μ := randomLabels (V := Fin n) r hr hrhalf
  let B := fun b : Bool => {ω : Fin n → Option Bool |
    2*r*n < ((univ.filter fun v => ω v = some b).card : ℝ)}
  let E := fun v : Fin n => {ω : Fin n → Option Bool |
    (((G.neighborFinset v).filter fun x => ω x = some false).card : ℝ) < r*G.degree v/2}
  let F := fun e : J => {ω : Fin n → Option Bool |
    (((P e).filter fun p => ∀ x ∈ pathInterior p, ω x = some true).card : ℝ) < c*n*r^(H-1)/4}
  have hB : ∀ b, μ.real (B b) ≤ exp (-2*r^2*n) := by
    intro b
    have hh := label_count_upper r hr hrhalf (univ : Finset (Fin n)) b
    simp only [card_univ, Fintype.card_fin] at hh
    have hsub : B b ⊆ {ω | 2*r*n ≤ ((univ.filter fun v => ω v = some b).card : ℝ)} := by
      intro ω h
      change 2*r*n < ((univ.filter fun v => ω v = some b).card : ℝ) at h
      exact h.le
    exact (measureReal_mono (μ := μ) hsub).trans hh
  have hE : ∀ v, μ.real (E v) ≤ exp (-c*r^2*n/2) := by
    intro v
    have hh := label_count_lower r hr hrhalf (G.neighborFinset v) false
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hsub : E v ⊆ {ω | (((G.neighborFinset v).filter fun x => ω x = some false).card : ℝ) ≤ r*G.degree v/2} := by
      intro ω h
      change (((G.neighborFinset v).filter fun x => ω x = some false).card : ℝ) < r*G.degree v/2 at h
      exact h.le
    apply ((measureReal_mono (μ := μ) hsub).trans hh).trans
    apply exp_le_exp.mpr
    have hd : c*n ≤ (G.degree v : ℝ) := hconn.trans (by exact_mod_cast vertexConnectivity_le_degree G v)
    nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg r)]
  have hF : ∀ e, μ.real (F e) ≤ exp (-c*n*(r^(H-1))^2/4) := by
    intro e
    have hh := path_survival_lower e.property (P e) (hPdisj e) (hPlen e) r hr hrhalf
    have hsub : F e ⊆ {ω | (((P e).filter fun p => ∀ x ∈ pathInterior p, ω x = some true).card : ℝ) ≤
        r^(H-1)*(P e).card/2} := by
      intro ω hω
      have hm := mul_le_mul_of_nonneg_right (hPcard e) (pow_nonneg hr (H-1))
      change _ < c*n*r^(H-1)/4 at hω
      change (((P e).filter fun p => ∀ x ∈ pathInterior p, ω x = some true).card : ℝ) ≤
        r^(H-1)*(P e).card/2
      nlinarith
    apply ((measureReal_mono hsub).trans hh).trans
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hPcard e) (sq_nonneg (r^(H-1)))]
  let A : (Bool ⊕ Fin n) ⊕ J → Set (Fin n → Option Bool) :=
    Sum.elim (Sum.elim B E) F
  have hJ : (Fintype.card J : ℝ) ≤ (n : ℝ)^2 := by
    have hh : Fintype.card J ≤ n*n := by
      calc
        _ ≤ Fintype.card (Fin n × Fin n) := Fintype.card_le_of_injective
          (fun e : J => e.val) Subtype.val_injective
        _ = _ := by simp
    simpa only [pow_two, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hh
  have hsum : (∑ i, μ.real (A i)) < 1 := by
    simp only [A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have hb := sum_le_sum (fun b (_ : b ∈ (univ : Finset Bool)) => hB b)
    have he := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin n))) => hE v)
    have hf := sum_le_sum (fun e (_ : e ∈ (univ : Finset J)) => hF e)
    simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_bool, Fintype.card_fin, Nat.cast_ofNat] at hb he hf
    have hj := mul_le_mul_of_nonneg_right hJ (exp_pos (-c*n*(r^(H-1))^2/4)).le
    have hfail : 2*exp (-2*r^2*n) + n*exp (-c*r^2*n/2) +
        (n : ℝ)^2*exp (-c*n*(r^(H-1))^2/4) < 1 := by simpa [H] using hfailure
    linarith
  obtain ⟨ω, hω⟩ := exists_avoiding_events μ A hsum
  let C := univ.filter fun v => ω v = some true
  let D := univ.filter fun v => ω v = some false
  refine ⟨C, D, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    simp_all
  · exact le_of_not_gt (hω (Sum.inl (Sum.inl true)))
  · exact le_of_not_gt (hω (Sum.inl (Sum.inl false)))
  · intro v
    have heq : D.filter (G.Adj v) = (G.neighborFinset v).filter fun x => ω x = some false := by
      ext x
      simp [D, and_comm]
    rw [heq]
    exact le_of_not_gt (hω (Sum.inl (Sum.inr v)))
  · intro u v huv
    let e : J := ⟨(u,v),huv⟩
    let Q := (P e).filter fun p => ∀ x ∈ pathInterior p, ω x = some true
    refine ⟨Q, le_of_not_gt (hω (Sum.inr e)), ?_, ?_⟩
    · intro p hp
      refine ⟨hPlen e p (mem_filter.mp hp).1, ?_⟩
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2 x hx⟩
    · intro p hp q hq hpq
      exact hPdisj e (mem_filter.mp hp).1 (mem_filter.mp hq).1 hpq

/-- A stronger reservoir theorem covering Lemma A.4, with the same sampling
rate and path-length bound. Its `c*n*r^(H-1)/4` paths give the manuscript's
`n*r^H` for all sufficiently large orders. The threshold depends only on c. -/
theorem exists_reservoirs (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      c*n ≤ (vertexConnectivity G : ℝ) →
      ∃ C D : Finset (Fin n),
        Reservoirs G c (1/log (log (n : ℝ))) (⌈2/c⌉₊+1) C D ∧
        ∀ v, c*(1/log (log (n : ℝ)))*n/2 ≤ ((D.filter (G.Adj v)).card : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (reservoir_failure_eventually_lt_one hc ⌈2/c⌉₊)
  refine ⟨max N 1, ?_⟩
  intro n hn G hconn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hr, hrhalf, hfailure⟩ := hN n hnN
  obtain ⟨C,D,hCD⟩ := reservoirs_of_failure_lt_one G hc (by omega) hr hrhalf hconn hfailure
  refine ⟨C,D,hCD,?_⟩
  intro v
  have hd : c*n ≤ (G.degree v : ℝ) := hconn.trans (by exact_mod_cast vertexConnectivity_le_degree G v)
  have hh := mul_le_mul_of_nonneg_left hd hr
  have hbound := hCD.2.2.2.1 v
  nlinarith

end HadwigerRamsey.ThomasonUpper
