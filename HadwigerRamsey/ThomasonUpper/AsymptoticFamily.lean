import HadwigerRamsey.ThomasonUpper.MultitypeAsymptotic
import HadwigerRamsey.ThomasonUpper.AsymptoticParameters
import HadwigerRamsey.ThomasonUpper.AsymptoticFiniteBounds
import HadwigerRamsey.ThomasonUpper.TrimmedEntropy
import HadwigerRamsey.ThomasonUpper.Trimming
import HadwigerRamsey.ThomasonUpper.RoundedScale

open scoped BigOperators Classical Topology
open Finset Real Filter

namespace HadwigerRamsey.ThomasonUpper

set_option maxHeartbeats 1600000

/-- The complete-family consequence of A.3 needed for Theorem 1.5.
Vertices discarded in the trimming step need not be added back, since
the final minor construction uses only the complete family. -/
theorem asymptotic_complete_family {a lambda eta : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hlambda : 0 < lambda)
    (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), ∀ k : ℕ, ∀ classes : Fin n → Fin k,
      (∀ i, a ≤ classMass classes i) →
      (∀ i j, a ≤ 1-blockDensity G classes i j) →
      lambda ≤ blockLambda classes (blockDensity G classes) →
      ∃ m : ℕ, ∃ W : Fin m → Finset (Fin n), 0 < m ∧
        (1-eta)*(n : ℝ)/sqrt (log (n : ℝ))*sqrt (blockLambda classes (blockDensity G classes)) ≤ m ∧
        (m : ℝ) ≤ C*n/sqrt (log (n : ℝ)) ∧
        (∀ i, (W i).Nonempty ∧ ((W i).card : ℝ) ≤ C*sqrt (log (n : ℝ))) ∧
        Pairwise (fun i j => Disjoint (W i) (W j)) ∧
        ∀ i j, i ≠ j → PartsJoined G (W i) (W j) := by
  obtain ⟨gamma,xi,tau,phi,omega,hgamma,hxi,hxi3,htau,htau1,hphi,hphi1,homega,
    hratio,hgain,htaucost,hphicost,homegacost⟩ := exists_multitype_asymptotic_parameters ha hlambda heta
  let c := 1-2*xi
  have hc : 0 < c := by dsimp only [c]; linarith only [hxi3]
  let g := c-(1-eta)*(1+gamma)
  have hg : 0 < g := by
    have hh := (lt_div_iff₀ (show 0 < 1+gamma by linarith only [hgamma])).mp hratio
    dsimp only [g,c]
    linarith only [hh]
  let d := min (min (a/4) (a^2/32)) (min (xi*lambda*a^2/64) (min (1/4) (g/(8*c))))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hda : d ≤ a/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hda2 : d ≤ a^2/32 := (min_le_left _ _).trans (min_le_right _ _)
  have hdxi : d ≤ xi*lambda*a^2/64 := (min_le_right _ _).trans (min_le_left _ _)
  have hdquarter : d ≤ 1/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdgain : d ≤ g/(8*c) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdsmall : d < a/2 := by linarith only [hda,ha]
  have hdq : 8*d/a ≤ a/2 := by apply (div_le_iff₀ ha).mpr; nlinarith only [hda2]
  have hdcost : 4*c*d ≤ g := by
    have hh := (le_div_iff₀ (show 0 < 8*c by positivity)).mp hdgain
    nlinarith only [hh,hg]
  have hlog : 0 ≤ log (2/a) := log_nonneg ((le_div_iff₀ ha).mpr (by linarith only [ha1]))
  let A := 1+4/a+2/(a*d)+4*log (2/a)/(a*xi*lambda)+(1+gamma)*(4/g)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAa0 : 0 ≤ 4/a := by positivity
  have hAd0 : 0 ≤ 2/(a*d) := by positivity
  have hAl0 : 0 ≤ 4*log (2/a)/(a*xi*lambda) := by positivity
  have hAg0 : 0 ≤ (1+gamma)*(4/g) := by positivity
  have hA4 : 4/a ≤ A := by dsimp only [A]; linarith only [hAa0,hAd0,hAl0,hAg0]
  have hAd : 2/(a*d) ≤ A := by dsimp only [A]; linarith only [hAa0,hAd0,hAl0,hAg0]
  have hAlog : 4*log (2/a)/(a*xi*lambda) ≤ A := by dsimp only [A]; linarith only [hAa0,hAd0,hAl0,hAg0]
  have hAg : 1+(1+gamma)*(4/g) ≤ A := by dsimp only [A]; linarith only [hAa0,hAd0,hAl0,hAg0]
  let B := log (1/a)+1
  have hB : 0 < B := by
    have hh : 0 ≤ log (1/a) := log_nonneg ((le_div_iff₀ ha).mpr (by simpa using ha1))
    dsimp only [B]
    linarith only [hh]
  let Cscale := (1+gamma)/sqrt lambda+1
  have hCscale : 0 < Cscale := by dsimp only [Cscale]; positivity
  let C := 1+sqrt B+Cscale/c
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  have hscale := eventually_rounded_scale hlambda hB hgamma.le hA (show 0 < d/2 by positivity)
  have hmany := multitype_many_parts_at_ambient_order (C := Cscale) (delta := 2*xi) (eta := 2*xi)
    ⌈1/a⌉₊ htau htau1 homega hphi hphi1 hCscale (by positivity) (by positivity)
    (by simpa using homegacost)
  filter_upwards [hscale,hmany,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (4/a),
    (eventually_ge_atTop 2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n)] with n hscale hmany hlogn han hn
  intro G k classes hmass hq hLambda
  change 1 ≤ log (n : ℝ) at hlogn
  change 4/a ≤ (n : ℝ) at han
  have hnN : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnN
  have han4 : 4 ≤ a*n := by simpa only [mul_comm] using (div_le_iff₀ ha).mp han
  have hsize : ∀ i, a*n ≤ (classVertices classes i).card :=
    fun i => (le_div_iff₀ hnR).mp (hmass i)
  have hk : 0 < k := by have := (classes ⟨0,hnN⟩).isLt; omega
  have hka : (k : ℝ)*a ≤ 1 := by
    calc
      _ = ∑ _i : Fin k, a := by simp
      _ ≤ ∑ i, classMass classes i := sum_le_sum (fun i _ => hmass i)
      _ = 1 := sum_classMass hnN classes
  have hkK : k ≤ ⌈1/a⌉₊ := by
    have hh : (k : ℝ) ≤ 1/a := (le_div_iff₀ ha).mpr hka
    exact_mod_cast hh.trans (Nat.le_ceil (1/a))
  let Lambda := blockLambda classes (blockDensity G classes)
  have hLampos : 0 < Lambda := hlambda.trans_le hLambda
  have hLamB : Lambda ≤ B := (blockLambda_le_complement_bound hnN G classes ha hq).trans (by dsimp [B]; linarith only [])
  let L := ⌈(1+gamma)*sqrt (log (n : ℝ)/Lambda)⌉₊
  obtain ⟨hL,hLA,hLupper,hLn,hLlower⟩ := hscale Lambda hLambda hLamB
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hlarge : 2 ≤ a*L := by
    have hh := (div_le_iff₀ ha).mp (hA4.trans hLA)
    linarith only [hh]
  have hfrac : 1/(a*(L : ℝ)) ≤ d/2 := by
    have hh := (div_le_iff₀ (mul_pos ha hd)).mp (hAd.trans hLA)
    apply (div_le_iff₀ (mul_pos ha hLR)).mpr
    nlinarith only [hh]
  have hscale4 : 4*L ≤ n := by
    have hh := (div_le_iff₀ hnR).mp hLn
    have hh' := mul_le_mul_of_nonneg_right hdquarter hnR.le
    have hr : (4 : ℝ)*L ≤ n := by nlinarith only [hh,hh']
    exact_mod_cast hr
  obtain ⟨m,s,X,hmpos,hmsum,hspos,hround,hX,hUcard,hloss⟩ :=
    rounded_class_trimming classes hnN hL ha hmass hlarge hscale4
  let U := univ.biUnion X
  let Z := univ \ U
  have hUn : U.card ≤ n := by simpa using card_le_univ U
  have hZcard : Z.card = n-U.card := by dsimp only [Z]; rw [card_sdiff_of_subset (subset_univ U),card_univ,Fintype.card_fin]
  have hN0 : n-Z.card = s*L := by change U.card = s*L at hUcard; omega
  have hZ : (Z.card : ℝ) ≤ d*n := by
    have hh : ((n : ℝ)-U.card)/n ≤ d := by linarith only [hloss,hfrac,hLn]
    rw [hZcard,Nat.cast_sub hUn]
    exact (div_le_iff₀ hnR).mp hh
  have hretain : (1-d)*(n : ℝ) ≤ (s : ℝ)*L := by
    have hh : (U.card : ℝ) = (s : ℝ)*L := by exact_mod_cast hUcard
    have hzR : (Z.card : ℝ) = (n : ℝ)-U.card := by rw [hZcard,Nat.cast_sub hUn]
    linarith only [hZ,hh,hzR]
  have hs2 : 2 ≤ s := by
    have hscaleR : (4 : ℝ)*L ≤ n := by exact_mod_cast hscale4
    have hsR : (2 : ℝ) ≤ s := by nlinarith only [hretain,hscaleR,hdquarter,hLR]
    exact_mod_cast hsR
  let G0 := restrictedGraph G Z
  let classes0 := restrictedClasses classes Z
  have hcard0 : ∀ i, (classVertices classes0 i).card = s*m i := by
    intro i
    have hh := congrArg Finset.card (image_restricted_class classes Z i)
    rw [card_image_of_injective _ (survivorMap_injective Z),
      trimmed_classes_eq_survivors classes X (fun i => (hX i).1)] at hh
    exact hh.trans (hX i).2
  let R := regularizedLambda (fun i => (m i : ℝ)/L)
    (fun i j => 1-deletedBlockDensity G classes Z i j) tau
  have hRident : regularizedLambda (fun i => (m i : ℝ)/L)
      (fun i j => 1-blockDensity G0 classes0 i j) tau = R := by
    simp only [G0,classes0,regularizedLambda,restrictedBlockDensity,R]
  have herr := rounded_deleted_entropy_error G classes Z m ha ha1 hd.le hdsmall han4 hZ hsize hq hdq
    hL hmsum hround htau.le
  have hden : 16*d/a^2 ≤ xi*lambda/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith only [hdxi,hd]
  have hweight : 2*log (2/a)/(a*L) ≤ xi*lambda/2 := by
    have hh := (div_le_iff₀ (mul_pos (mul_pos ha hxi) hlambda)).mp (hAlog.trans hLA)
    apply (div_le_iff₀ (mul_pos ha hLR)).mpr
    nlinarith only [hh]
  have hRlower : (1-2*xi)*Lambda ≤ R := by
    have hh := (abs_le.mp herr).1
    change -(tau/a+16*d/a^2+2*log (2/a)/(a*L)) ≤ R-Lambda at hh
    nlinarith only [hh,htaucost,hden,hweight,hLambda,hxi]
  have hphinet : phi*(-log tau) ≤ xi*Lambda := by
    have hh := hphicost
    rw [one_div,log_inv] at hh
    nlinarith only [hh,hLambda,hxi]
  have hquad := rounded_quadratic_entropy_margin hLampos (by linarith only [hlogn] : 0 ≤ log (n : ℝ))
    hgamma.le hxi3 hLlower hRlower hphinet hgain.le
  rw [← hRident] at hquad
  obtain ⟨t,W,ht,hts,htlower,hW⟩ := hmany k hk hkK (n-Z.card) (Nat.sub_le _ _) G0 classes0 m s hs2
    hmpos hcard0 L hL hmsum hLupper hquad
  have hcount : (1-eta)*(n : ℝ)/sqrt (log (n : ℝ)/Lambda) ≤ t := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (1+gamma)*sqrt (log (n : ℝ)/Lambda) by positivity)
    change (L : ℝ) < _ at hceil
    have hgT : 4 ≤ g*sqrt (log (n : ℝ)/Lambda) := by
      have hh : (1+gamma)*(4/g) < (1+gamma)*sqrt (log (n : ℝ)/Lambda) := by linarith only [hAg.trans hLA,hceil]
      have hh' := (mul_lt_mul_iff_right₀ (show 0 < 1+gamma by linarith only [hgamma])).mp hh
      have hh'' := (div_lt_iff₀ hg).mp hh'
      nlinarith only [hh'']
    exact part_count_from_trimmed_scale hc heta heta1 (by linarith only [hdquarter] : d < 1)
      (sqrt_pos.mpr (div_pos (by linarith only [hlogn]) hLampos)) hgT hdcost hceil hretain htlower
  have hroot : 0 < sqrt (log (n : ℝ)) := sqrt_pos.mpr (by linarith only [hlogn])
  have hrootB : 0 < sqrt B := sqrt_pos.mpr hB
  have hrootLam : 0 < sqrt Lambda := sqrt_pos.mpr hLampos
  have hcount' : (1-eta)*(n : ℝ)/sqrt (log (n : ℝ))*sqrt Lambda ≤ t := by
    rw [sqrt_div (by linarith only [hlogn]) Lambda] at hcount
    convert hcount using 1 <;> field_simp
  have hLroot : sqrt (log (n : ℝ)) ≤ (L : ℝ)*sqrt B := by
    conv_lhs at hLlower => rw [sqrt_div (by linarith only [hlogn]) Lambda,← mul_div_assoc]
    have hh := (div_le_iff₀ hrootLam).mp hLlower
    have hh' := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hLamB) hLR.le
    nlinarith only [hh,hh',mul_nonneg hgamma.le hroot.le]
  have htupper : (t : ℝ) ≤ C*n/sqrt (log (n : ℝ)) := by
    apply (le_div_iff₀ hroot).mpr
    have htsR : (t : ℝ) ≤ s := by exact_mod_cast hts
    have hsL : (s : ℝ)*L ≤ n := by exact_mod_cast (hN0 ▸ Nat.sub_le n Z.card)
    have hh := mul_le_mul_of_nonneg_left hLroot (show (0 : ℝ) ≤ s by positivity)
    have hh' := mul_le_mul_of_nonneg_right hsL hrootB.le
    have hh'' := mul_le_mul_of_nonneg_right htsR hroot.le
    have hCB : sqrt B ≤ C := by
      dsimp only [C]
      linarith only [div_nonneg hCscale.le hc.le]
    nlinarith only [hh,hh',hh'',mul_le_mul_of_nonneg_right hCB hnR.le]
  let W' := fun i => (W i).image (survivorMap Z)
  refine ⟨t,W',ht,hcount',htupper,?_,?_,?_⟩
  · intro i
    refine ⟨(hW.nonempty i).image _,?_⟩
    rw [show (W' i).card = (W i).card from card_image_of_injective _ (survivorMap_injective Z)]
    have hp := part_size_from_many_parts hW hspos hN0 hc htlower i
    have hfracL := div_le_div_of_nonneg_right hLupper hc.le
    change (L : ℝ)/c ≤ Cscale*sqrt (log (n : ℝ))/c at hfracL
    rw [mul_div_right_comm] at hfracL
    have hroot1 : 1 ≤ sqrt (log (n : ℝ)) := (one_le_sqrt).mpr hlogn
    have hCC : Cscale/c+1 ≤ C := by dsimp only [C]; linarith only [sqrt_nonneg B]
    have hh : ((W i).card : ℝ) ≤ (Cscale/c+1)*sqrt (log (n : ℝ)) := by nlinarith only [hp,hfracL,hroot1]
    exact hh.trans (mul_le_mul_of_nonneg_right hCC hroot.le)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,hxv⟩ := mem_image.mp hv
    obtain ⟨y,hy,hyv⟩ := mem_image.mp hw
    have hxy := survivorMap_injective Z (hxv.trans hyv.symm)
    exact Finset.disjoint_left.mp (hW.disjoint hij) hx (hxy.symm ▸ hy)
  · intro i j hij
    obtain ⟨u,hu,v,hv,huv⟩ := hW.complete i j hij
    exact ⟨survivorMap Z u,mem_image_of_mem _ hu,survivorMap Z v,mem_image_of_mem _ hv,huv⟩

end HadwigerRamsey.ThomasonUpper
