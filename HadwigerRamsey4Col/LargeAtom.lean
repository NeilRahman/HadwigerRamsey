import HadwigerRamsey4Col.Program
import HadwigerRamsey4Col.Parameters

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col
namespace PairingData

lemma diagonal_cost_bound (I : PairingData) (i : Fin 4) :
    (3/2 : ℝ)*log (3/2) ≤ cost (I.span i i) +
      (1/2 : ℝ)*∑ j ∈ univ.erase i, cost (I.diag i j) := by
  have hspan := cost_tangent (I.span_lt_one i i) (show (0:ℝ)<1 by norm_num)
  norm_num [cost] at hspan
  change I.span i i ≤ cost (I.span i i) at hspan
  have ht : ∀ j ∈ univ.erase i,
      log (3/2)+(3/2 : ℝ)*I.diag i j-1/2 ≤ cost (I.diag i j) := by
    intro j hj
    have h := cost_tangent (I.diag_lt_one i j (ne_of_mem_erase hj).symm)
      (show (1/3:ℝ)<1 by norm_num)
    rw [cost_third] at h
    norm_num at h
    linarith
  have h := sum_le_sum ht
  have hcard : (univ.erase i).card = 3 := by simp
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
    ← mul_sum, hcard, Nat.cast_ofNat] at h
  have hs := I.diag_sum i
  have hn := I.span_nonneg i i
  linarith

lemma star_le_span (I : PairingData) (i : Fin 4) :
    I.mass i^2*cost (I.span i i) +
      2*∑ j ∈ univ.erase i, I.mass i*I.mass j*cost (I.span i j) ≤ I.spanEnergy := by
  let M := fun u v => I.mass u*I.mass v*cost (I.span u v)
  have hsym : ∀ u v, M u v = M v u := by
    intro u v
    dsimp [M]
    rw [I.span_symm u v]
    ring
  have hn : ∀ u v, 0 ≤ M u v := fun u v =>
    mul_nonneg (mul_nonneg (I.mass_nonneg u) (I.mass_nonneg v))
      (cost_nonneg (I.span_nonneg u v) (I.span_lt_one u v))
  have he : (∑ u, ∑ v, M u v) = M i i +
      2*(∑ j ∈ univ.erase i, M i j) +
      ∑ u ∈ univ.erase i, ∑ v ∈ univ.erase i, M u v := by
    have row := fun u => sum_erase_add univ (M u) (mem_univ i)
    rw [← sum_erase_add univ (fun u => ∑ v, M u v) (mem_univ i)]
    simp_rw [← row]
    simp only [sum_add_distrib]
    have hs : (∑ u ∈ univ.erase i, M u i) = ∑ u ∈ univ.erase i, M i u := by
      apply sum_congr rfl
      intro u hu
      exact hsym u i
    rw [hs]
    ring
  have hrest : 0 ≤ ∑ u ∈ univ.erase i, ∑ v ∈ univ.erase i, M u v :=
    sum_nonneg (fun u _ => sum_nonneg (fun v _ => hn u v))
  change _ ≤ ∑ u, ∑ v, M u v
  rw [he]
  dsimp [M] at *
  nlinarith

lemma weighted_star_bound (I : PairingData) (i : Fin 4) :
    (3/2 : ℝ)*log (3/2)*(I.mass i)^2 +
      (3*log (3/2)+log 2)*I.mass i*(1-I.mass i) ≤
      I.spanEnergy+(1/2 : ℝ)*∑ j ∈ univ.erase i, I.pairEnergy i j := by
  have hd := mul_le_mul_of_nonneg_left (I.diagonal_cost_bound i) (sq_nonneg (I.mass i))
  have ho : ∀ j ∈ univ.erase i,
      (I.mass i*I.mass j)*(3*log (3/2)+log 2) ≤
        2*I.mass i*I.mass j*cost (I.span i j)+
          I.mass i*I.mass j*cost (I.pair i j) := by
    intro j hj
    have hij := (ne_of_mem_erase hj).symm
    have h := two_cost_bound (I.span_lt_one i j) (I.pair_lt_one i j hij)
      (I.offdiag_sum i j hij)
    have hm : 0 ≤ 2*I.mass i*I.mass j :=
      mul_nonneg (mul_nonneg (by norm_num) (I.mass_nonneg i)) (I.mass_nonneg j)
    have hh := mul_le_mul_of_nonneg_left h hm
    nlinarith
  have ho' := sum_le_sum ho
  have hr := I.star_le_span i
  have hn : 0 ≤ ∑ j ∈ univ.erase i, I.mass j^2*cost (I.diag j i) := by
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (sq_nonneg _) (cost_nonneg
      (I.diag_nonneg j i (ne_of_mem_erase hj)) (I.diag_lt_one j i (ne_of_mem_erase hj)))
  have hm : (∑ j ∈ univ.erase i, I.mass j) = 1-I.mass i := by
    have := sum_erase_add univ I.mass (mem_univ i)
    rw [I.mass_sum] at this
    linarith
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul] at hd ho'
  simp only [pairEnergy, sum_add_distrib, ← mul_sum]
  rw [hm] at ho'
  have hfactor (q : Fin 4 → ℝ) :
      (∑ j ∈ univ.erase i, 2*I.mass i*I.mass j*q j) =
        2*∑ j ∈ univ.erase i, I.mass i*I.mass j*q j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [hfactor] at ho'
  rw [hfactor]
  nlinarith

/-- Lemma 3, in the stronger form that the rational threshold suffices. -/
theorem large_atom_of_threshold (I : PairingData)
    (hspan : I.spanEnergy ≤ (2213/10000 : ℝ))
    (hpairs : ∀ i j, i ≠ j → I.pairEnergy i j ≤ (2213/10000 : ℝ)) :
    ∀ i, I.mass i < (2/5 : ℝ) := by
  intro i
  have hx0 := I.mass_nonneg i
  have hx1 : I.mass i ≤ 1 := by
    have h := single_le_sum (fun j _ => I.mass_nonneg j) (mem_univ i)
    rwa [I.mass_sum] at h
  have hb := I.weighted_star_bound i
  have hp : (∑ j ∈ univ.erase i, I.pairEnergy i j) ≤ 3*(2213/10000 : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ univ.erase i, (2213/10000 : ℝ) :=
        sum_le_sum (fun j hj => hpairs i j (ne_of_mem_erase hj).symm)
      _ = _ := by norm_num
  obtain ⟨hl0,hl1⟩ := log_lower_bounds
  have hprod : 0 ≤ I.mass i*(1-I.mass i) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hb0 := mul_le_mul_of_nonneg_right hl0.le (sq_nonneg (I.mass i))
  have hb1 := mul_le_mul_of_nonneg_right hl0.le hprod
  have hb2 := mul_le_mul_of_nonneg_right hl1.le hprod
  by_contra hnot
  have hx : (2/5 : ℝ) ≤ I.mass i := le_of_not_gt hnot
  have hh := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx1)
  nlinarith

end PairingData

/-- Lemma 3 of the analytic manuscript, for its algebraic parameter `p`. -/
theorem lemma3 (I : PairingData) {p : ℝ} (hp : 0 < p)
    (hpoly : 3*p^6+2*p-2=0) (hspan : I.spanEnergy ≤ tStar p)
    (hpairs : ∀ i j, i ≠ j → I.pairEnergy i j ≤ tStar p) :
    ∀ i, I.mass i < (2/5 : ℝ) := by
  have ht := tStar_lt_threshold hp hpoly
  exact I.large_atom_of_threshold (hspan.trans ht.le)
    (fun i j hij => (hpairs i j hij).trans ht.le)

/-- Lemma 3 with the manuscript's uniquely defined parameter. -/
theorem lemma3_at_optimum (I : PairingData)
    (hspan : I.spanEnergy ≤ tStar parameter)
    (hpairs : ∀ i j, i ≠ j → I.pairEnergy i j ≤ tStar parameter) :
    ∀ i, I.mass i < (2/5 : ℝ) :=
  lemma3 I parameter_spec.1 parameter_spec.2.2 hspan hpairs

end HadwigerRamsey4Col
