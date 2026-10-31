import HadwigerRamsey.ThomasonUpper.ReservoirExistence
import HadwigerRamsey.ThomasonUpper.ReservoirDomination
import HadwigerRamsey.ThomasonUpper.ConnectedCores
import HadwigerRamsey.ThomasonUpper.AllocationBudgets

open scoped BigOperators Classical
open Finset Real Filter

namespace HadwigerRamsey.ThomasonUpper

/-- The finite final construction in Theorem 1.5. A complete family outside
the reservoirs becomes a clique minor once the two explicit allocation
budgets hold. Reservoir existence and the budgets are separate checked steps. -/
theorem cliqueMinor_of_reservoirs {n m K H : ℕ} (G : SimpleGraph (Fin n))
    (W : Fin m → Finset (Fin n)) (C D : Finset (Fin n)) {ε r : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r)
    (hres : Reservoirs G ε r H C D)
    (hdeg : ∀ v, ε*r*n/2 ≤ ((D.filter (G.Adj v)).card : ℝ))
    (hW : ∀ a, (W a).Nonempty) (hWK : ∀ a, (W a).card ≤ K)
    (hWdisj : ∀ a b, a ≠ b → Disjoint (W a) (W b))
    (hWC : ∀ a, Disjoint (W a) C) (hWD : ∀ a, Disjoint (W a) D)
    (hcomplete : ∀ a b, a ≠ b → ∃ u ∈ W a, ∃ v ∈ W b, G.Adj u v)
    (hdomBudget : (m : ℝ)*(⌈log (K : ℝ)/(-log (1-ε/8))⌉₊+1) ≤ ε*r*n/4)
    (hpathBudget : ((H-1)*(m*(⌈log (K : ℝ)/(-log (1-ε/8))⌉₊+1)) : ℕ) < ε*n*r^(H-1)/4) :
    HasCliqueMinor G m := by
  classical
  let L := ⌈log (K : ℝ)/(-log (1-ε/8))⌉₊+1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨M, hM, hMdisj⟩ := reservoir_dominating_sets G W D K hW hWK ε (r*n)
    hε hε1 (mul_pos hr hnR) (by nlinarith [hres.2.2.1])
    (fun _ v _ => by nlinarith [hdeg v]) (by
      simpa only [Fintype.card_fin, mul_assoc] using hdomBudget)
  have hMnon : ∀ a, (M a).Nonempty := by
    intro a
    obtain ⟨v,hv⟩ := hW a
    obtain ⟨u,hu,_⟩ := (hM a).2.2 v hv
    exact ⟨u,hu⟩
  obtain ⟨S,hS,hSdisj⟩ := connected_reservoir_cores G M C D hMnon
    (fun a => (hM a).1) (fun a => (hM a).2.1) hMdisj hres.1
    (by simpa only [L] using hpathBudget)
    (fun u _ v _ huv => by
      obtain ⟨P,hcard,hlen,hd⟩ := hres.2.2.2.2 u v huv
      exact ⟨P,hcard,hlen,hd⟩)
  apply cliqueMinor_of_complete_dominated (fun a => (W a : Set (Fin n))) S
    (fun a => (hS a).2.1)
  · intro a v hv
    obtain ⟨u,hu,hadj⟩ := (hM a).2.2 v hv
    exact ⟨u,(hS a).1 hu,hadj⟩
  · intro a b hab
    have hWS : ∀ a b, Disjoint (W a : Set (Fin n)) (S b) := by
      intro a b
      apply Set.disjoint_left.mpr
      intro x hxW hxS
      rcases (hS b).2.2 hxS with hxM | hxC
      · exact Finset.disjoint_left.mp (hWD a) hxW ((hM b).1 hxM)
      · exact Finset.disjoint_left.mp (hWC a) hxW hxC
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Finset.disjoint_left.mp (hWdisj a b hab) hx hy
    · exact Set.disjoint_left.mp (hWS a b) hx hy
    · exact Set.disjoint_left.mp (hWS b a) hy hx
    · exact Set.disjoint_left.mp (hSdisj a b hab) hx hy
  · exact hcomplete

/-- The final half of Theorem 1.5 with no reservoir or allocation-budget
assumptions: choose the reservoirs first, then any sufficiently small
complete family outside them yields the claimed-size clique minor. The
uniform order threshold depends only on epsilon and the size constant. -/
theorem reservoirs_complete_family_to_minor {ε B : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hB : 0 < B) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      ε*n ≤ (vertexConnectivity G : ℝ) →
      ∃ C D : Finset (Fin n),
        Reservoirs G ε (1/log (log (n : ℝ))) (⌈2/ε⌉₊+1) C D ∧
        ∀ m K : ℕ, ∀ W : Fin m → Finset (Fin n),
          1 ≤ K → (K : ℝ) ≤ B*sqrt (log (n : ℝ)) →
          (m : ℝ) ≤ B*n/sqrt (log (n : ℝ)) →
          (∀ a, (W a).Nonempty ∧ (W a).card ≤ K) →
          (∀ a b, a ≠ b → Disjoint (W a) (W b)) →
          (∀ a, Disjoint (W a) C ∧ Disjoint (W a) D) →
          (∀ a b, a ≠ b → ∃ u ∈ W a, ∃ v ∈ W b, G.Adj u v) →
          HasCliqueMinor G m := by
  classical
  obtain ⟨Nr,hNr⟩ := exists_reservoirs ε hε
  obtain ⟨Nb,hNb⟩ := Filter.eventually_atTop.mp
    (eventually_reservoir_allocation_budgets hε hε1 hB (⌈2/ε⌉₊+1) (by omega))
  have ht := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  obtain ⟨Nt,hNt⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max (max Nr Nb) (max Nt 1), ?_⟩
  intro n hn G hconn
  have hrN : Nr ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hbN : Nb ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have htN : Nt ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hloglog : 1 ≤ log (log (n : ℝ)) := hNt n htN
  have hr : 0 < 1/log (log (n : ℝ)) := by positivity
  obtain ⟨C,D,hres,hdeg⟩ := hNr n hrN G hconn
  refine ⟨C,D,hres,?_⟩
  intro m K W hK hKB hm hW hd hsep hcomplete
  obtain ⟨hdom,hpath⟩ := hNb n hbN m K hK hKB hm
  simp only [Nat.cast_add,Nat.cast_one] at hdom
  exact cliqueMinor_of_reservoirs G W C D (by omega) hε hε1 hr hres hdeg
    (fun a => (hW a).1) (fun a => (hW a).2) hd
    (fun a => (hsep a).1) (fun a => (hsep a).2) hcomplete hdom hpath

end HadwigerRamsey.ThomasonUpper
