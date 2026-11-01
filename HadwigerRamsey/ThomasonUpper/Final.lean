import HadwigerRamsey.ThomasonUpper.AsymptoticFamily
import HadwigerRamsey.ThomasonUpper.CappedRestriction
import HadwigerRamsey.ThomasonUpper.DensityLower
import HadwigerRamsey.ThomasonUpper.FiniteAssembly
import HadwigerRamsey.ThomasonUpper.FinalScale
import HadwigerRamsey.ThomasonUpper.FinalEventually

open scoped BigOperators Classical Topology
open Finset Real Filter

namespace HadwigerRamsey.ThomasonUpper

set_option maxHeartbeats 1800000

/-- Theorem 1.5 of the manuscript, with the exact capped ordered double
sum and the additive error outside the square root. -/
theorem thomasonupper : Statement := by
  intro epsilon hepsilon
  by_cases hepsilon1 : epsilon < 1
  · let q := epsilon*(1-epsilon)
    have hq : 0 < q := by dsimp only [q]; positivity
    let B := log (1/epsilon)+1
    have hB : 0 < B := by
      have hh : 0 ≤ log (1/epsilon) := log_nonneg ((le_div_iff₀ hepsilon).mpr (by linarith))
      dsimp only [B]
      linarith only [hh]
    let eta := min (1/4) (epsilon/(8*(sqrt B+1)))
    have heta : 0 < eta := by dsimp only [eta]; positivity
    have hetaq : eta ≤ 1/4 := min_le_left _ _
    have heta1 : eta < 1 := by linarith only [hetaq]
    have hetacost : 4*eta*sqrt B ≤ epsilon := by
      have hh := (le_div_iff₀ (show 0 < 8*(sqrt B+1) by positivity)).mp (min_le_right (1/4) (epsilon/(8*(sqrt B+1))))
      change eta*(8*(sqrt B+1)) ≤ epsilon at hh
      nlinarith only [hh,heta,sqrt_nonneg B]
    let E := 16/epsilon^2+4*log (2/epsilon)/epsilon
    have hlog : 0 ≤ log (2/epsilon) := log_nonneg ((le_div_iff₀ hepsilon).mpr (by linarith))
    have hE : 0 < E := by dsimp only [E]; positivity
    let d := min eta (min (epsilon/4) (min (epsilon^2/32)
      (min (1/4) (min (q/(4*E)) ((epsilon/4)^2/(2*E))))))
    have hd : 0 < d := by dsimp only [d]; positivity
    have hdeta : d ≤ eta := min_le_left _ _
    have hda : d ≤ epsilon/4 := (min_le_right _ _).trans (min_le_left _ _)
    have hda2 : d ≤ epsilon^2/32 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hdquarter : d ≤ 1/4 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hdq : d ≤ q/(4*E) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hderr : d ≤ (epsilon/4)^2/(2*E) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    let e := min (q/4) ((epsilon/4)^2/2)
    have he : 0 < e := by dsimp only [e]; positivity
    obtain ⟨C,hC,hfamily⟩ := asymptotic_complete_family (a := epsilon/2) (lambda := q/4) (eta := eta)
      (by positivity) (by linarith) (by positivity) heta heta1
    obtain ⟨NA,hNA⟩ := eventually_atTop.mp hfamily
    obtain ⟨NR,hNR⟩ := reservoirs_complete_family_to_minor hepsilon hepsilon1 (show 0 < 2*C+2 by positivity)
    have hfinal := eventually_final_error_bounds hepsilon hd he
    have hnlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (4/epsilon)
    have hall : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
        epsilon*n ≤ (vertexConnectivity G : ℝ) → ∀ k : ℕ, ∀ classes : Fin n → Fin k,
        (∀ i, epsilon ≤ classMass classes i) →
        (n : ℝ)/sqrt (log (n : ℝ))*(sqrt (cappedLambda G classes epsilon)-epsilon) ≤ (hadwigerNumber G : ℝ) := by
      filter_upwards [hfinal,hnlarge,eventually_ge_atTop NR,eventually_ge_atTop (2*NA+4)] with n hf hlarge hnR hnA
      intro G hconn k classes hmass
      obtain ⟨hlogn,hdelta0,hdeltad,hcaperr⟩ := hf
      change 4/epsilon ≤ (n : ℝ) at hlarge
      have hnN : 0 < n := by omega
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hnN
      have hsize : 4 ≤ epsilon*n := by simpa only [mul_comm] using (div_le_iff₀ hepsilon).mp hlarge
      have hGamma := cappedLambda_lower hnN G classes hepsilon hepsilon1.le
        (class_size_two hnN classes hmass (by linarith only [hsize])) hconn
      have hGammaB : cappedLambda G classes epsilon ≤ B := (cappedLambda_le hnN G classes hepsilon hepsilon1.le).trans (by dsimp only [B]; linarith)
      obtain ⟨Cr,Dr,hres,hminor⟩ := hNR n hnR G hconn
      let Z := Cr ∪ Dr
      let delta := 4/log (log (n : ℝ))
      have hdelta : 0 ≤ delta := hdelta0
      have hdeltaeta : delta ≤ eta := hdeltad.trans hdeta
      have hdeltas : delta < epsilon/2 := by linarith only [hdeltad,hda,hepsilon]
      have hdeltaq : 8*delta/epsilon ≤ epsilon/2 := by
        apply (div_le_iff₀ hepsilon).mpr
        nlinarith only [hdeltad,hda2]
      have hdeltaquarter : delta ≤ 1/4 := hdeltad.trans hdquarter
      have hZ : (Z.card : ℝ) ≤ delta*n := by
        have hh : (Z.card : ℝ) ≤ (Cr.card : ℝ)+Dr.card := by exact_mod_cast card_union_le Cr Dr
        have hCr := hres.2.1
        have hDr := hres.2.2.1
        calc
          _ ≤ (Cr.card : ℝ)+Dr.card := hh
          _ ≤ 2*(1/log (log (n : ℝ)))*n+2*(1/log (log (n : ℝ)))*n := add_le_add hCr hDr
          _ = delta*n := by dsimp only [delta]; ring
      obtain ⟨H,hHG,hZn,hmass0,hq0,herr0⟩ := exists_capped_restriction G classes Z hepsilon hepsilon1.le
        hdelta hdeltas hdeltaq hsize hZ hmass
      let N := n-Z.card
      have hNn : N ≤ n := Nat.sub_le _ _
      have hNRcast : (N : ℝ) = (n : ℝ)-Z.card := by dsimp only [N]; rw [Nat.cast_sub (Nat.le_of_lt hZn)]
      have hretained : (1-delta)*(n : ℝ) ≤ N := by nlinarith only [hZ,hNRcast]
      have hn2N : n ≤ 2*N := by
        have hh : (n : ℝ) ≤ 2*(N : ℝ) := by nlinarith only [hretained,hdeltaquarter,hnpos]
        exact_mod_cast hh
      have hNcut : NA ≤ N := by omega
      have hN2 : 2 ≤ N := by omega
      obtain ⟨hrootN,hrootNn,hrootnN⟩ := sqrt_log_order_comparison hN2 hNn hn2N
      have hroot : 0 < sqrt (log (n : ℝ)) := hrootN.trans_le hrootNn
      have hroot1 : 1 ≤ sqrt (log (n : ℝ)) := one_le_sqrt.mpr hlogn
      let G0 := restrictedGraph H Z
      let classes0 := restrictedClasses classes Z
      let R := blockLambda classes0 (blockDensity G0 classes0)
      have herrorQ : |R-cappedLambda G classes epsilon| ≤ q/2 := by
        have hh := (le_div_iff₀ (show 0 < 4*E by positivity)).mp (hdeltad.trans hdq)
        have heq : e ≤ q/4 := min_le_left _ _
        change |R-cappedLambda G classes epsilon| ≤ _ at herr0
        change 4/(epsilon^3*(n : ℝ)^2) ≤ e at hcaperr
        dsimp only [E] at hh
        nlinarith only [herr0,hcaperr,hh,heq]
      have herror : |R-cappedLambda G classes epsilon| ≤ (epsilon/4)^2 := by
        have hh := (le_div_iff₀ (show 0 < 2*E by positivity)).mp (hdeltad.trans hderr)
        have hee : e ≤ (epsilon/4)^2/2 := min_le_right _ _
        dsimp only [E] at hh
        nlinarith only [herr0,hcaperr,hh,hee]
      have hR : q/4 ≤ R := by
        have hh := (abs_le.mp herrorQ).1
        nlinarith only [hh,hGamma,hq]
      have hR0 : 0 ≤ R := (by positivity : 0 ≤ q/4).trans hR
      obtain ⟨m,W,hmpos,hmlower,hmupper,hW,hdW,hcomplete⟩ := hNA N hNcut G0 k classes0 hmass0 hq0 hR
      let W' : Fin m → Finset (Fin n) := fun i => (W i).image (survivorMap Z)
      have hW' : ∀ i, (W' i).Nonempty ∧ ((W' i).card : ℝ) ≤ C*sqrt (log (n : ℝ)) := by
        intro i
        refine ⟨(hW i).1.image _,?_⟩
        rw [show (W' i).card = (W i).card from card_image_of_injective _ (survivorMap_injective Z)]
        exact (hW i).2.trans (mul_le_mul_of_nonneg_left hrootNn hC.le)
      have hdisjoint : ∀ i j, i ≠ j → Disjoint (W' i) (W' j) := by
        intro i j hij
        apply Finset.disjoint_left.mpr
        intro v hv hw
        obtain ⟨x,hx,hxv⟩ := mem_image.mp hv
        obtain ⟨y,hy,hyv⟩ := mem_image.mp hw
        have hxy := survivorMap_injective Z (hxv.trans hyv.symm)
        exact Finset.disjoint_left.mp (hdW hij) hx (hxy.symm ▸ hy)
      have hsep : ∀ i, Disjoint (W' i) Cr ∧ Disjoint (W' i) Dr := by
        intro i
        have hh : Disjoint (W' i) Z := by
          apply Finset.disjoint_left.mpr
          intro v hv hz
          obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
          exact survivorMap_not_mem Z x hz
        exact ⟨hh.mono_right Finset.subset_union_left,hh.mono_right Finset.subset_union_right⟩
      have hjoined : ∀ i j, i ≠ j → PartsJoined G (W' i) (W' j) := by
        intro i j hij
        obtain ⟨u,hu,v,hv,huv⟩ := hcomplete i j hij
        exact ⟨survivorMap Z u,mem_image_of_mem _ hu,survivorMap Z v,mem_image_of_mem _ hv,hHG huv⟩
      let K := ⌈C*sqrt (log (n : ℝ))⌉₊
      have hK : 1 ≤ K := Nat.ceil_pos.mpr (mul_pos hC hroot)
      have hKbound : (K : ℝ) ≤ (2*C+2)*sqrt (log (n : ℝ)) := by
        have hh := Nat.ceil_lt_add_one (mul_nonneg hC.le hroot.le)
        change (K : ℝ) < C*sqrt (log (n : ℝ))+1 at hh
        nlinarith only [hh,hroot1,hC,hroot]
      have hKparts : ∀ i, (W' i).Nonempty ∧ (W' i).card ≤ K := by
        intro i
        refine ⟨(hW' i).1,?_⟩
        exact_mod_cast (hW' i).2.trans (Nat.le_ceil (C*sqrt (log (n : ℝ))))
      have hmB : (m : ℝ) ≤ (2*C+2)*n/sqrt (log (n : ℝ)) := by
        apply (le_div_iff₀ hroot).mpr
        have hh := (le_div_iff₀ hrootN).mp hmupper
        have hh' := mul_le_mul_of_nonneg_left hrootnN (show (0 : ℝ) ≤ m by positivity)
        have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
        have hh'' := mul_le_mul_of_nonneg_left hNnR hC.le
        nlinarith only [hh,hh',hh'',hnpos]
      have hminorG := hminor m K W' hK hKbound hmB hKparts hdisjoint hsep hjoined
      have hmHad : (m : ℝ) ≤ hadwigerNumber G := by exact_mod_cast cliqueMinor_le_hadwigerNumber hminorG
      have hrootacc := final_entropy_accuracy (cappedLambda_nonneg G classes hepsilon hepsilon1.le)
        hR0 hGammaB hepsilon heta.le heta1 hdelta hdeltaeta hetacost herror
      have hscale : (1-eta)*(1-delta)*(n : ℝ)/sqrt (log (n : ℝ))*sqrt R ≤ m := by
        have hnon : 0 ≤ (1-eta)*sqrt R := mul_nonneg (by linarith only [heta1]) (sqrt_nonneg R)
        have hNdiv : (N : ℝ)/sqrt (log (n : ℝ)) ≤ N/sqrt (log (N : ℝ)) := by
          exact div_le_div_of_nonneg_left (by positivity) hrootN hrootNn
        have hretdiv := div_le_div_of_nonneg_right hretained hroot.le
        have hh := mul_le_mul_of_nonneg_left (hretdiv.trans hNdiv) hnon
        change (1-eta)*(N : ℝ)/sqrt (log (N : ℝ))*sqrt R ≤ m at hmlower
        calc
          _ = (1-eta)*sqrt R*((1-delta)*(n : ℝ)/sqrt (log (n : ℝ))) := by ring
          _ ≤ (1-eta)*sqrt R*((N : ℝ)/sqrt (log (N : ℝ))) := hh
          _ = (1-eta)*(N : ℝ)/sqrt (log (N : ℝ))*sqrt R := by ring
          _ ≤ m := hmlower
      have hh := mul_le_mul_of_nonneg_left hrootacc (div_nonneg hnpos.le hroot.le)
      exact (show (n : ℝ)/sqrt (log (n : ℝ))*(sqrt (cappedLambda G classes epsilon)-epsilon) ≤ m by
        calc
          _ ≤ (n : ℝ)/sqrt (log (n : ℝ))*((1-eta)*(1-delta)*sqrt R) := hh
          _ = (1-eta)*(1-delta)*(n : ℝ)/sqrt (log (n : ℝ))*sqrt R := by ring
          _ ≤ m := hscale).trans hmHad
    obtain ⟨N,hN⟩ := eventually_atTop.mp hall
    exact ⟨N,fun n hn G hconn k classes hmass => hN n hn G hconn k classes hmass⟩
  · refine ⟨1,?_⟩
    intro n hn G hconn k classes hmass
    exact False.elim (hepsilon1 (connectivity_excludes_large_epsilon (by omega) G hconn))

end HadwigerRamsey.ThomasonUpper
