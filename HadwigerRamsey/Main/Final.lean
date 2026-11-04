import HadwigerRamsey.Main.Contradiction
import HadwigerRamsey.Main.Parameters
import HadwigerRamsey.Main.GraphCaps
import HadwigerRamsey.TwoBigSets
import HadwigerRamsey.DenseMinor

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper HadwigerRamsey.ControlledPartition
namespace HadwigerRamsey.Main
set_option maxHeartbeats 1500000

theorem third_colour (i j : Fin 3) (hij : i≠j) :
    ∃ k : Fin 3, i≠k ∧ j≠k := by
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | exact ⟨0,by decide,by decide⟩ |
    exact ⟨1,by decide,by decide⟩ | exact ⟨2,by decide,by decide⟩

theorem choose_good_set {n : ℕ} (G : SimpleGraph (Fin n)) {e δ : ℝ}
    (he : 0≤e) (hgood : TwoBigSets.Good G e δ) :
    ∃ P : Finset (Fin n), (1-e)*n≤(P.card:ℝ) ∧
      (((G.edgeFinset.card:ℝ)≤3*e*(n:ℝ)^2 ∧ P=univ) ∨ RealConnected G P (δ*n)) := by
  rcases hgood with hs | ⟨P,hP,hc⟩
  · refine ⟨univ,?_,Or.inl ⟨hs,rfl⟩⟩
    simp only [card_univ,Fintype.card_fin]
    nlinarith only [mul_nonneg he (Nat.cast_nonneg n)]
  · exact ⟨P,hP,Or.inr hc⟩

theorem mainthm_small (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ G : Fin 3→SimpleGraph (Fin n), IsThreeDecomposition G →
      ∃ i : Fin 3, (1-ε)*beta*n/sqrt (log (n:ℝ))≤(hadwigerNumber (G i):ℝ) := by
  obtain ⟨lam,hl,hls,hleps,htail⟩ := choose_lam hε
  have hK : 0<2*beta/lam := by have := beta_pos; positivity
  obtain ⟨γB,hγB,NB,hNB,hbip⟩ := bipMinor (2*beta/lam) hK
  obtain ⟨γD,hγD,ND,hND,hdense⟩ := denseMinor (2*beta/lam) hK
  let ζ := min γB (min γD (min (lam/2) (beta/100)))
  have hz : 0<ζ := by dsimp [ζ]; have:=beta_pos; positivity
  have hzB : ζ≤γB := min_le_left _ _
  have hzD : ζ≤γD := (min_le_right _ _).trans (min_le_left _ _)
  have hzl : ζ≤lam/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hzb : ζ≤beta/100 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ξ,hx,hopt⟩ := optapprox ζ hz
  obtain ⟨e,η,he,hη,hex,hee,hez,hηx⟩ := choose_small hε hl hz hx
  obtain ⟨NBIG,hNBIG,δ₀,hδ₀,hbig⟩ := twobigsets e beta he beta_pos
  obtain ⟨δ,hδ,hpartition⟩ := connectedsets lam η hl hη
  let θ := min (δ₀/2) (min δ ζ)
  have ht : 0<θ := by dsimp [θ]; positivity
  have htd₀ : θ≤δ₀/2 := min_le_left _ _
  have htd : θ≤δ := (min_le_right _ _).trans (min_le_left _ _)
  have htz : θ≤ζ := (min_le_right _ _).trans (min_le_right _ _)
  have htl : θ≤lam/2 := htz.trans hzl
  obtain ⟨NT,hthom⟩ := thomasonupper θ ht
  let M := max (max ND NB) NT
  let L := max NBIG (max (2*NT) (max 4 (max ⌈2*(M+2:ℕ)/lam⌉₊ (max ⌈10/lam⌉₊ ⌈1/e⌉₊))))
  refine ⟨L,?_⟩
  intro n hn G hG
  have hnBIG : NBIG≤n := (le_max_left _ _).trans hn
  have hnNT : 2*NT≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn4 : 4≤n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnL : max ⌈2*(M+2:ℕ)/lam⌉₊ (max ⌈10/lam⌉₊ ⌈1/e⌉₊)≤n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hroot : 0<sqrt (log (n:ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast (by omega : 1<n)))
  have hcutM : ((M+2:ℕ):ℝ)≤lam/2*n := by
    have hh : 2*(M+2:ℕ)/lam≤(n:ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_left _ _).trans hnL)
    have hh' := (div_le_iff₀ hl).mp hh
    nlinarith only [hh']
  have hlarge : 10≤lam*n := by
    have hh : 10/lam≤(n:ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hnL))
    nlinarith only [(div_le_iff₀ hl).mp hh]
  have horder : 1/(n:ℝ)≤e := by
    have hh : 1/e≤(n:ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hnL))
    have hh' := (div_le_iff₀ he).mp hh
    apply (div_le_iff₀ hnR).mpr
    nlinarith only [hh']
  by_contra! hbad
  have hnorm : ∀ c, (hadwigerNumber (G c):ℝ)*sqrt (log (n:ℝ))/(n:ℝ)≤(1-ε)*beta := by
    intro c
    apply (div_le_iff₀ hnR).mpr
    exact ((lt_div_iff₀ hroot).mp (hbad c)).le
  have hsmall : ∀ c, (hadwigerNumber (G c):ℝ)<beta*n/sqrt (log (n:ℝ)) := by
    intro c
    apply (hbad c).trans
    apply (div_lt_div_iff_of_pos_right hroot).mpr
    have hb:=beta_pos
    nlinarith only [mul_pos hε (mul_pos hb hnR)]
  have hcaps := fun c => set_density_caps (G c) hl hzD hzB
    (show ((max ND NB+2:ℕ):ℝ)≤lam/2*n from
      (show ((max ND NB+2:ℕ):ℝ)≤(M+2:ℕ) by exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 2).trans hcutM)
    hdense hbip (hsmall c)
  rcases hbig n hnBIG G hG with ⟨i,j,hij,hGi,hGj⟩ | ⟨c,hc⟩
  · obtain ⟨k,hik,hjk⟩ := third_colour i j hij
    obtain ⟨P,hP,hPB⟩ := choose_good_set (G i) he.le hGi
    obtain ⟨Q,hQ,hQG⟩ := choose_good_set (G j) he.le hGj
    obtain ⟨D⟩ := partitionData_exists (G k) (Classical.choose (hpartition n (G k))) hn hl hls hη.le
      (Classical.choose_spec (hpartition n (G k)))
    exact optimization_contradiction G hG i j k hij hik hjk hε hε1 hl hls hleps he hη.le
      hex hee hez hηx hz hzl hzb hx ht htl htd htd₀ htz htail hlarge
      (show (NT:ℝ)≤lam/2*n from (show (NT:ℝ)≤(M+2:ℕ) by
        exact_mod_cast (le_max_right (max ND NB) NT).trans (Nat.le_add_right M 2)).trans hcutM)
      hnNT hn4 horder hthom hopt D P Q hP hQ hPB hQG hnorm hcaps
  · exact (not_lt_of_ge hc) (hsmall c)

end HadwigerRamsey.Main
