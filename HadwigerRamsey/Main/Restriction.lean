import HadwigerRamsey.Main.Entropy

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper HadwigerRamsey.ControlledPartition
namespace HadwigerRamsey.Main

noncomputable def restrictedDensity {n m : ℕ} (G : SimpleGraph (Fin n))
    (V : Fin (m+1) → Finset (Fin n)) (P : Finset (Fin n)) (i j : Fin m) : ℝ :=
  if i=j then internalDensity G (V i.castSucc ∩ P)
  else (G.edgeDensity (V i.castSucc ∩ P) (V j.castSucc ∩ P) : ℝ)

theorem restrictedDensity_nonneg {n m : ℕ} (G : SimpleGraph (Fin n))
    (V : Fin (m+1) → Finset (Fin n)) (P : Finset (Fin n)) (i j : Fin m) :
    0 ≤ restrictedDensity G V P i j := by
  unfold restrictedDensity
  split
  · exact internalDensity_nonneg _ _
  · exact_mod_cast G.edgeDensity_nonneg _ _

theorem restrictedDensity_symm {n m : ℕ} (G : SimpleGraph (Fin n))
    (V : Fin (m+1) → Finset (Fin n)) (P : Finset (Fin n)) (i j : Fin m) :
    restrictedDensity G V P i j = restrictedDensity G V P j i := by
  unfold restrictedDensity
  by_cases hij : i=j
  · subst j; rfl
  · simp only [if_neg hij,if_neg (Ne.symm hij)]
    rw [G.edgeDensity_comm]

noncomputable def setClasses {n k : ℕ} (τ : Fin n → Fin k)
    (P : Finset (Fin n)) : Fin P.card → Fin k :=
  fun v => τ (P.equivFin.symm v).val

lemma image_setClasses {n k : ℕ} (τ : Fin n → Fin k)
    (P : Finset (Fin n)) (i : Fin k) :
    (classVertices (setClasses τ P) i).image (fun v => (P.equivFin.symm v).val) =
      classVertices τ i ∩ P := by
  classical
  ext v
  simp only [mem_image,classVertices,mem_filter,mem_univ,true_and,mem_inter]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨hu,(P.equivFin.symm u).property⟩
  · rintro ⟨hi,hv⟩
    refine ⟨P.equivFin ⟨v,hv⟩,?_,?_⟩
    · simpa [setClasses] using hi
    · simp

noncomputable def activeClasses {n m : ℕ} (τ : Fin n → Fin (m+1))
    (P : Finset (Fin n)) (hno : ∀ v ∈ P, τ v ≠ Fin.last m) : Fin P.card → Fin m :=
  fun u => ⟨(τ (P.equivFin.symm u).val).val,by
    have hh := (τ (P.equivFin.symm u).val).isLt
    have hn := hno _ (P.equivFin.symm u).property
    have hv : (τ (P.equivFin.symm u).val).val ≠ m := by
      intro he
      exact hn (Fin.ext he)
    omega⟩

lemma activeClasses_eq {n m : ℕ} (τ : Fin n → Fin (m+1))
    (P : Finset (Fin n)) (hno : ∀ v ∈ P, τ v ≠ Fin.last m)
    (u : Fin P.card) (i : Fin m) :
    activeClasses τ P hno u = i ↔ setClasses τ P u = i.castSucc := by
  constructor
  · intro hh
    apply Fin.ext
    simpa only [activeClasses,setClasses,Fin.val_castSucc] using congrArg Fin.val hh
  · intro hh
    apply Fin.ext
    simpa only [activeClasses,setClasses,Fin.val_castSucc] using congrArg Fin.val hh

lemma image_activeClasses {n m : ℕ} (τ : Fin n → Fin (m+1))
    (P : Finset (Fin n)) (hno : ∀ v ∈ P, τ v ≠ Fin.last m) (i : Fin m) :
    (classVertices (activeClasses τ P hno) i).image (fun v => (P.equivFin.symm v).val) =
      classVertices τ i.castSucc ∩ P := by
  have he : classVertices (activeClasses τ P hno) i = classVertices (setClasses τ P) i.castSucc := by
    ext u
    simp only [classVertices,mem_filter,mem_univ,true_and]
    exact activeClasses_eq τ P hno u i
  rw [he,image_setClasses]

lemma classMass_of_image {n d k : ℕ} (f : Fin d → Fin n) (hf : Function.Injective f)
    (σ : Fin d → Fin k) (i : Fin k) (S : Finset (Fin n))
    (himage : (classVertices σ i).image f = S) :
    classMass σ i = (S.card : ℝ)/d := by
  have hc : (classVertices σ i).card = S.card := by
    rw [←himage,card_image_of_injective _ hf]
  change ((classVertices σ i).card : ℝ)/(d : ℝ) = _
  rw [hc]

lemma density_of_images {n d k : ℕ} (G : SimpleGraph (Fin n))
    (f : Fin d → Fin n) (hf : Function.Injective f) (σ : Fin d → Fin k)
    (S : Fin k → Finset (Fin n)) (himage : ∀ i, (classVertices σ i).image f = S i)
    (i j : Fin k) :
    blockDensity (G.comap f) σ i j =
      if i=j then internalDensity G (S i) else (G.edgeDensity (S i) (S j) : ℝ) := by
  unfold blockDensity
  split
  · rw [internalDensity_comap G f hf,himage]
  · rw [edgeDensity_comap G f hf,himage,himage]

lemma intersection_retained_fraction {n : ℕ} {lam e : ℝ} (hlam : 0 < lam) (he : 0 ≤ e)
    (S P : Finset (Fin n)) (hS : lam*n ≤ (S.card : ℝ))
    (hP : (1-e)*n ≤ (P.card : ℝ)) :
    (1-e/lam)*(S.card : ℝ) ≤ (S ∩ P).card := by
  have hPn : P.card ≤ n := by simpa using P.card_le_univ
  have hc : ((univ \ P : Finset (Fin n)).card : ℝ) = (n : ℝ)-P.card := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,Nat.cast_sub hPn]
  have hsub : S \ P ⊆ univ \ P := sdiff_subset_sdiff (subset_univ _) Subset.rfl
  have hloss : ((S \ P).card : ℝ) ≤ e*n := by
    have hh : ((S \ P).card : ℝ) ≤ (univ \ P : Finset (Fin n)).card := by exact_mod_cast card_le_card hsub
    rw [hc] at hh
    nlinarith only [hh,hP]
  have hsum : ((S ∩ P).card : ℝ)+(S \ P).card = S.card := by
    exact_mod_cast card_inter_add_card_sdiff S P
  have hmul := mul_le_mul_of_nonneg_left hS (div_nonneg he hlam.le)
  have hcancel : (e/lam)*(lam*(n : ℝ)) = e*n := by field_simp
  rw [hcancel] at hmul
  nlinarith only [hloss,hsum,hmul]

end HadwigerRamsey.Main

namespace HadwigerRamsey.Main

lemma enumeration_injective {n : ℕ} (P : Finset (Fin n)) :
    Function.Injective (fun u : Fin P.card => (P.equivFin.symm u).val) := by
  intro i j hij
  exact P.equivFin.symm.injective (Subtype.ext hij)

/-- Removing a small dummy class preserves the active intersections. -/
lemma active_intersection_delete_dummy {n m : ℕ} (τ : Fin n → Fin (m+1))
    (P : Finset (Fin n)) (i : Fin m) :
    classVertices τ i.castSucc ∩ (P \ classVertices τ (Fin.last m)) =
      classVertices τ i.castSucc ∩ P := by
  ext v
  simp only [classVertices,mem_inter,mem_sdiff,mem_filter,mem_univ,true_and]
  have hi : i.castSucc ≠ Fin.last m := by
    intro he
    have hh := congrArg Fin.val he
    exact Nat.ne_of_lt i.isLt hh
  aesop

/-- The near-spanning set still contains at least half the ambient vertices
when the last exceptional class is discarded. -/
lemma nearspanning_delete_size {n : ℕ} {lam e : ℝ}
    (hlam : lam ≤ 1/100) (he : e ≤ lam)
    (P D : Finset (Fin n)) (hP : (1-e)*n ≤ (P.card : ℝ))
    (hD : (D.card : ℝ) ≤ 21*lam*n) :
    (n : ℝ)/2 ≤ (P \ D).card := by
  have hh : (P.card : ℝ) ≤ (P \ D).card + (D.card : ℝ) := by
    exact_mod_cast (card_le_card_sdiff_add_card : P.card ≤ (P \ D).card+D.card)
  have hne := mul_le_mul_of_nonneg_right he (show (0 : ℝ) ≤ n by positivity)
  have hnlam := mul_le_mul_of_nonneg_right hlam (show (0 : ℝ) ≤ n by positivity)
  nlinarith only [hh,hP,hD,hne,hnlam]

end HadwigerRamsey.Main

namespace HadwigerRamsey.Main

/-- Apply the induced-graph entropy bound after a restriction which preserves
all active intersections with the original near-spanning set. -/
theorem entropy_on_restriction {n m N k : ℕ} (G : SimpleGraph (Fin n))
    {lam e θ : ℝ} (hlam : 0 < lam) (he : 0 ≤ e) (helam : e ≤ lam)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hthom : ThomasonBound θ N)
    (hnN : 2*N ≤ n) (hn4 : 4 ≤ n)
    (V : Fin (m+1) → Finset (Fin n)) (P R : Finset (Fin n))
    (hsize : ∀ i : Fin m, lam*n ≤ ((V i.castSucc).card : ℝ))
    (hP : (1-e)*n ≤ (P.card : ℝ)) (hR : (n : ℝ)/2 ≤ R.card)
    (hconn : RealConnected G R (θ*R.card))
    (σ : Fin R.card → Fin k) (hmassall : ∀ j, θ ≤ classMass σ j)
    (f : Fin m → Fin k) (hf : Function.Injective f)
    (himage : ∀ i, (classVertices σ (f i)).image (fun u => (R.equivFin.symm u).val) =
      V i.castSucc ∩ P)
    (hcap : ∀ i j, restrictedDensity G V P i j ≤ 1-θ) :
    (1-e/lam)*sqrt (Optimization.energy (fun i : Fin m => ((V i.castSucc).card : ℝ)/n)
      (restrictedDensity G V P)) ≤
      (hadwigerNumber G : ℝ)*sqrt (log (n : ℝ))/(n : ℝ)+θ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hR2 : 2 ≤ R.card := by
    have hh : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    exact_mod_cast (show (2 : ℝ) ≤ R.card by linarith only [hh,hR])
  have hNR : N ≤ R.card := by
    have hh : 2*(N : ℝ) ≤ n := by exact_mod_cast hnN
    exact_mod_cast (show (N : ℝ) ≤ R.card by linarith only [hh,hR])
  have hRR : (0 : ℝ) < R.card := by exact_mod_cast (by omega : 0 < R.card)
  have hc : 0 ≤ 1-e/lam := by
    have hh := (div_le_one hlam).mpr helam
    linarith
  apply induced_entropy_upper G hθ hθ1 hc hthom R hR2 hNR hconn σ hmassall f hf
    (fun i : Fin m => ((V i.castSucc).card : ℝ)/n) (restrictedDensity G V P)
    (by intro i; positivity) ?_ ?_ hcap
  · intro i
    rw [classMass_of_image _ (enumeration_injective R) σ (f i) _ (himage i)]
    have hh := div_le_div_of_nonneg_right
      (intersection_retained_fraction hlam he (V i.castSucc) P (hsize i) hP) hRR.le
    convert hh using 1 <;> first | rfl | field_simp
  · intro i j
    unfold restrictedDensity blockDensity
    by_cases hij : i=j
    · subst j
      simp only [ite_true]
      unfold inducedGraph
      rw [internalDensity_comap G _ (enumeration_injective R),himage]
    · simp only [if_neg hij,if_neg (hf.ne hij)]
      unfold inducedGraph
      rw [edgeDensity_comap G _ (enumeration_injective R),himage,himage]

/-- The near-spanning connected-colour step of the manuscript. The final class
is retained when large enough for Theorem 1.5, and otherwise is deleted. -/
theorem nearspanning_entropy_upper {n m N : ℕ} (G : SimpleGraph (Fin n))
    {lam e θ δ₀ : ℝ} (hlam : 0 < lam) (hlamsmall : lam ≤ 1/100)
    (he : 0 ≤ e) (helam : e ≤ lam/2) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hθlam : θ ≤ lam/2) (hθδ : θ ≤ δ₀/2) (hthom : ThomasonBound θ N)
    (hnN : 2*N ≤ n) (hn4 : 4 ≤ n)
    (V : Fin (m+1) → Finset (Fin n)) (τ : Fin n → Fin (m+1))
    (hV : ∀ i, classVertices τ i = V i)
    (hsize : ∀ i : Fin m, lam*n ≤ ((V i.castSucc).card : ℝ))
    (hdummy : ((V (Fin.last m)).card : ℝ) ≤ 21*lam*n)
    (P : Finset (Fin n)) (hP : (1-e)*n ≤ (P.card : ℝ))
    (hconn : RealConnected G P (δ₀*n))
    (hcap : ∀ i j, restrictedDensity G V P i j ≤ 1-θ) :
    (1-e/lam)*sqrt (Optimization.energy (fun i : Fin m => ((V i.castSucc).card : ℝ)/n)
      (restrictedDensity G V P)) ≤
      (hadwigerNumber G : ℝ)*sqrt (log (n : ℝ))/(n : ℝ)+θ := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have helam' : e ≤ lam := by linarith
  have hδ : 0 < δ₀ := by linarith
  let D := P ∩ V (Fin.last m)
  have hDsub : D ⊆ V (Fin.last m) := inter_subset_right
  have hDcard : (D.card : ℝ) ≤ 21*lam*n := by
    exact (show (D.card : ℝ) ≤ (V (Fin.last m)).card by exact_mod_cast card_le_card hDsub).trans hdummy
  have hmass_active : ∀ i : Fin m, (lam/2)*n ≤ ((V i.castSucc ∩ P).card : ℝ) := by
    intro i
    have hh : (V i.castSucc).card ≤ (V i.castSucc ∩ P).card + (univ \ P : Finset (Fin n)).card := by
      have hsum := card_inter_add_card_sdiff (V i.castSucc) P
      have hsub : V i.castSucc \ P ⊆ univ \ P := sdiff_subset_sdiff (subset_univ _) Subset.rfl
      have hsubcard := card_le_card hsub
      omega
    have hPn : P.card ≤ n := by simpa using P.card_le_univ
    have hc : ((univ \ P : Finset (Fin n)).card : ℝ) = (n : ℝ)-P.card := by
      rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,Nat.cast_sub hPn]
    have hhR : ((V i.castSucc).card : ℝ) ≤ (V i.castSucc ∩ P).card + (univ \ P : Finset (Fin n)).card := by exact_mod_cast hh
    rw [hc] at hhR
    have heN := mul_le_mul_of_nonneg_right helam hnR.le
    nlinarith only [hhR,hP,hsize i,heN]
  by_cases hlarge : (δ₀/2)*n ≤ (D.card : ℝ)
  · let σ := setClasses τ P
    have hPsize : (n : ℝ)/2 ≤ P.card := by
      have hh := nearspanning_delete_size hlamsmall helam' P (∅ : Finset (Fin n)) hP
        (show ((∅ : Finset (Fin n)).card : ℝ) ≤ 21*lam*n by simp; positivity)
      simpa using hh
    have hPconn : RealConnected G P (θ*P.card) := hconn.mono (by
      have hPn : (P.card : ℝ) ≤ n := by exact_mod_cast (by simpa using P.card_le_univ : P.card ≤ n)
      have hh := mul_le_mul_of_nonneg_left hPn hθ.le
      have hh' := mul_le_mul_of_nonneg_right hθδ hnR.le
      have hd0 := mul_nonneg hδ.le hnR.le
      nlinarith only [hh,hh',hd0])
    have hmassall : ∀ j, θ ≤ classMass σ j := by
      intro j
      have hPR : (0 : ℝ) < P.card := by linarith only [hPsize,hnR]
      rw [classMass_of_image _ (enumeration_injective P) σ j _ (image_setClasses τ P j),hV]
      apply (le_div_iff₀ hPR).mpr
      have hPn : (P.card : ℝ) ≤ n := by exact_mod_cast (by simpa using P.card_le_univ : P.card ≤ n)
      have hh := mul_le_mul_of_nonneg_left hPn hθ.le
      by_cases hj : j = Fin.last m
      · subst j
        have heq : V (Fin.last m) ∩ P = D := inter_comm _ _
        rw [heq]
        have hh' := mul_le_mul_of_nonneg_right hθδ hnR.le
        nlinarith only [hh,hh',hlarge]
      · have hjm : j.val < m := by
          have hv : j.val ≠ m := fun hv => hj (Fin.ext hv)
          omega
        let i : Fin m := ⟨j.val,hjm⟩
        have heq : i.castSucc = j := Fin.ext rfl
        rw [←heq]
        have hh' := mul_le_mul_of_nonneg_right hθlam hnR.le
        nlinarith only [hh,hh',hmass_active i]
    apply entropy_on_restriction G hlam he helam' hθ hθ1 hthom hnN hn4 V P P hsize hP hPsize
      hPconn σ hmassall Fin.castSucc (Fin.castSucc_injective m) ?_ hcap
    intro i
    simpa only [hV] using image_setClasses τ P i.castSucc
  · let R := P \ V (Fin.last m)
    have hRsize : (n : ℝ)/2 ≤ R.card := nearspanning_delete_size hlamsmall helam' P _ hP hdummy
    have hno : ∀ v ∈ R, τ v ≠ Fin.last m := by
      intro v hv heq
      have hvnot := (mem_sdiff.mp hv).2
      apply hvnot
      rw [←hV]
      exact mem_filter.mpr ⟨mem_univ _,heq⟩
    let σ := activeClasses τ R hno
    have himage : ∀ i : Fin m, (classVertices σ i).image (fun u => (R.equivFin.symm u).val) =
        V i.castSucc ∩ P := by
      intro i
      rw [image_activeClasses]
      change classVertices τ i.castSucc ∩ (P \ V (Fin.last m)) = _
      rw [←hV,active_intersection_delete_dummy,hV]
    have hRconn : RealConnected G R (θ*R.card) := by
      have hh := hconn.delete D
      have heq : P \ D = R := by ext v; simp [D,R]
      rw [heq] at hh
      apply hh.mono
      have hRn : (R.card : ℝ) ≤ n := by exact_mod_cast (by simpa using R.card_le_univ : R.card ≤ n)
      have hh' := mul_le_mul_of_nonneg_left hRn hθ.le
      have hhδ := mul_le_mul_of_nonneg_right hθδ hnR.le
      have hsmall : (D.card : ℝ) < (δ₀/2)*n := lt_of_not_ge hlarge
      nlinarith only [hh',hhδ,hsmall]
    have hmassall : ∀ j, θ ≤ classMass σ j := by
      intro j
      have hRR : (0 : ℝ) < R.card := by linarith only [hRsize,hnR]
      rw [classMass_of_image _ (enumeration_injective R) σ j _ (himage j)]
      apply (le_div_iff₀ hRR).mpr
      have hRn : (R.card : ℝ) ≤ n := by exact_mod_cast (by simpa using R.card_le_univ : R.card ≤ n)
      have hh := mul_le_mul_of_nonneg_left hRn hθ.le
      have hh' := mul_le_mul_of_nonneg_right hθlam hnR.le
      nlinarith only [hh,hh',hmass_active j]
    exact entropy_on_restriction G hlam he helam' hθ hθ1 hthom hnN hn4 V P R hsize hP hRsize
      hRconn σ hmassall id Function.injective_id himage hcap

end HadwigerRamsey.Main
