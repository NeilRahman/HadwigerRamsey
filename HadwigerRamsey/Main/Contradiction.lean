import HadwigerRamsey.Main.Configuration
import HadwigerRamsey.Main.Feasibility
import HadwigerRamsey.Main.LocalCosts
import HadwigerRamsey.Main.ColourEnergy

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper HadwigerRamsey.ControlledPartition
namespace HadwigerRamsey.Main
set_option maxHeartbeats 1000000

theorem optimization_contradiction {n N : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    {ε lam η δ δ₀ e ζ ξ θ : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hl : 0<lam) (hls : lam≤1/100)
    (hleps : lam≤ε*beta/100) (he : 0<e) (hη : 0≤η)
    (hex : e≤lam*ξ/100) (hee : e≤lam*ε/100) (hez : e≤ζ*beta^2/100)
    (hηx : η/lam≤ξ/4) (hz : 0<ζ) (hzl : ζ≤lam/2) (hzb : ζ≤beta/100)
    (hx : 0<ξ) (ht : 0<θ) (htl : θ≤lam/2) (htd : θ≤δ)
    (htd₀ : θ≤δ₀/2) (htz : θ≤ζ)
    (htail : 42*lam*log 2≤ε*beta^2/10)
    (hlarge : 10≤lam*n) (hcut : (N:ℝ)≤lam/2*n)
    (hnN : 2*N≤n) (hn4 : 4≤n) (horder : 1/(n:ℝ)≤e)
    (hthom : ThomasonBound θ N) (hopt : ApproxBound ζ ξ)
    (D : PartitionData (G k) lam η δ)
    (P Q : Finset (Fin n)) (hP : (1-e)*n≤(P.card:ℝ)) (hQ : (1-e)*n≤(Q.card:ℝ))
    (hPB : ((G i).edgeFinset.card:ℝ)≤3*e*(n:ℝ)^2 ∧ P=univ ∨ RealConnected (G i) P (δ₀*n))
    (hQG : ((G j).edgeFinset.card:ℝ)≤3*e*(n:ℝ)^2 ∧ Q=univ ∨ RealConnected (G j) Q (δ₀*n))
    (hsmall : ∀ c, (hadwigerNumber (G c):ℝ)*sqrt (log (n:ℝ))/(n:ℝ)≤(1-ε)*beta)
    (hcaps : ∀ c : Fin 3,
      (∀ S : Finset (Fin n), lam/2*n≤(S.card:ℝ) → internalDensity (G c) S≤1-ζ) ∧
      (∀ S T : Finset (Fin n), Disjoint S T → lam/2*n≤(S.card:ℝ) →
        lam/2*n≤(T.card:ℝ) → ((G c).edgeDensity S T:ℝ)≤1-ζ)) : False := by
  have hn : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hhalf : ∀ u : Fin D.m, lam/2*n≤((D.V u.castSucc).card:ℝ) := by
    intro u
    have hh:=D.active_size u
    nlinarith only [hh,mul_pos hl hnR]
  have hcards : ∀ u : Fin D.m, 2≤(D.V u.castSucc).card := by
    intro u
    have hh:=D.active_size u
    exact_mod_cast (show (2:ℝ)≤(D.V u.castSucc).card by linarith)
  have hNs : ∀ u : Fin D.m, N≤(D.V u.castSucc).card := by
    intro u
    exact_mod_cast hcut.trans (hhalf u)
  have hel : e≤lam/2 := by
    have hh := mul_le_mul_of_nonneg_left hε1 hl.le
    nlinarith only [hee,hh,hl]
  have hz1 : ζ<1 := by linarith
  have ht1 : θ≤1 := by linarith
  have hze : ζ≤ε*beta/100 := by linarith
  have hte : θ≤ε*beta/100 := htz.trans hze
  have htzε : θ+ζ≤ε*beta := by
    have hb:=beta_pos
    nlinarith only [htz,hzl,hleps,mul_pos hε hb]
  have hinter : ∀ R : Finset (Fin n), (1-e)*n≤(R.card:ℝ) →
      ∀ u : Fin D.m, lam/2*n≤((D.V u.castSucc ∩ R).card:ℝ) := by
    intro R hR u
    have hh := intersection_retained_fraction hl he.le (D.V u.castSucc) R (D.active_size u) hR
    have hdiv : e/lam≤1/2 := (div_le_iff₀ hl).mpr (by linarith only [hel])
    have hm := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (D.V u.castSucc).card)
    have hs:=D.active_size u
    nlinarith only [hh,hm,hs]
  let α := classMass D.classes
  let p := fun u : Fin D.m => internalDensity (G k) (D.V u.castSucc)
  let qB := restrictedDensity (G i) D.V P
  let qG := restrictedDensity (G j) D.V Q
  have hαeq : ∀ u, α u = ((D.V u).card:ℝ)/n :=
    classMass_eq_card D.V D.classes D.classVertices_classes
  have hpcap : ∀ u, p u≤1-ζ := fun u => (hcaps k).1 _ (hhalf u)
  have hqcap : ∀ c : Fin 3, ∀ R, (1-e)*n≤(R.card:ℝ) →
      ∀ u v, restrictedDensity (G c) D.V R u v≤1-ζ := by
    intro c R hR u v
    by_cases huv : u=v
    · subst v
      simpa [restrictedDensity] using (hcaps c).1 _ (hinter R hR u)
    · rw [restrictedDensity,if_neg huv]
      apply (hcaps c).2 _ _ ?_ (hinter R hR u) (hinter R hR v)
      exact (D.pairwise ((Fin.castSucc_injective _).ne huv)).mono inter_subset_left inter_subset_left
  have hBcap : ∀ u v, qB u v≤1-ζ := hqcap i P hP
  have hGcap : ∀ u v, qG u v≤1-ζ := hqcap j Q hQ
  have hcost := active_cost_bounds (G k) D hn hl hlarge hε ht ht1 htd htzε hzb hthom
    hNs hcards (fun u => (hpcap u).trans (by linarith)) (hsmall k)
  have hc : ∀ u, α u.castSucc*sqrt (-log (1-p u))≤beta-ζ := by
    intro u
    simpa only [p,hαeq] using hcost u
  have heB := colour_energy_gap (G i) hε hε1 hl hls he.le hel hee hz hz1 hez ht ht1
    htl htd₀ htz hte hthom hnN hn4 horder D.V D.classes D.classVertices_classes
    D.active_size D.dummy_size P hP hPB hBcap (hsmall i)
  have heG := colour_energy_gap (G j) hε hε1 hl hls he.le hel hee hz hz1 hez ht ht1
    htl htd₀ htz hte hthom hnN hn4 horder D.V D.classes D.classVertices_classes
    D.active_size D.dummy_size Q hQ hQG hGcap (hsmall j)
  have hE : ∀ q : Fin D.m→Fin D.m→ℝ,
      Optimization.energy (fun u => α u.castSucc) q≤(1-ε/2)*beta^2 →
      sqrt (Optimization.energy α (fillMatrix q))≤beta-ζ := by
    intro q hq
    apply full_energy_gap hε hε1 hz.le hze hq
    have hh := fillMatrix_energy_bound α (D.mass_sum hn) q
    have hd:=D.mass_dummy hn
    have hm:=mul_le_mul_of_nonneg_right hd (show (0:ℝ)≤2*log 2 by positivity)
    nlinarith only [hh,hm,htail]
  have hEB := hE qB (by simpa only [hαeq,qB] using heB)
  have hEG := hE qG (by simpa only [hαeq,qG] using heG)
  have hfeas := density_feasibility G hG i j k hij hik hjk D P Q hl he.le hx.le hex hηx hP hQ hcards
  have hcount : (D.m+1:ℝ)≤1/ζ := by
    apply D.count.trans
    apply (div_le_div_iff₀ hl hz).mpr
    linarith only [hzl]
  exact configuration_contradiction hopt hx.le (by linarith) hzb α p qB qG
    D.mass_nonneg (D.mass_sum hn) hcount (fun u => internalDensity_nonneg _ _)
    hpcap (restrictedDensity_nonneg _ _ _) hBcap (restrictedDensity_nonneg _ _ _) hGcap
    (restrictedDensity_symm _ _ _) (restrictedDensity_symm _ _ _)
    hfeas.1 hfeas.2 hc hEB hEG

end HadwigerRamsey.Main
