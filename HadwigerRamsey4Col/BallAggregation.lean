import HadwigerRamsey4Col.BallEntropyBasic
import HadwigerRamsey4Col.BallNumerics

open Real Finset
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
namespace HadwigerRamsey4Col

lemma sum_group_weighted {α δ : Type} [Fintype α] [Fintype δ] [DecidableEq δ]
    (w : α → ℝ) (χ : α → δ) (f : δ → ℝ) :
    (∑ i, w i*f (χ i)) = ∑ u, (∑ i with χ i=u, w i)*f u := by
  rw [← sum_fiberwise univ χ (fun i => w i*f (χ i))]
  apply sum_congr rfl
  intro u _
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

lemma sum_group_pairs {α δ : Type} [Fintype α] [Fintype δ] [DecidableEq δ]
    (w : α → ℝ) (χ : α → δ) (f : δ → δ → ℝ) :
    (∑ i, ∑ j, w i*w j*f (χ i) (χ j)) =
      ∑ u, ∑ v, (∑ i with χ i=u,w i)*(∑ j with χ j=v,w j)*f u v := by
  calc
    _ = ∑ i, w i*(∑ j,w j*f (χ i) (χ j)) := by
      simp_rw [mul_sum,mul_assoc]
    _ = ∑ i, w i*(∑ v,(∑ j with χ j=v,w j)*f (χ i) v) := by
      apply sum_congr rfl
      intro i _
      rw [sum_group_weighted w χ (fun v => f (χ i) v)]
    _ = ∑ u,(∑ i with χ i=u,w i)*(∑ v,(∑ j with χ j=v,w j)*f u v) :=
      sum_group_weighted w χ (fun u => ∑ v,(∑ j with χ j=v,w j)*f u v)
    _ = _ := by
      apply sum_congr rfl
      intro u _
      rw [mul_sum]
      apply sum_congr rfl
      intro v _
      ring

lemma ballBase_sum (m : Option (Fin 4) → ℝ) :
    (∑ u, ∑ v, m u*m v*ballBase u v) =
      ballA*(∑ c,m (some c))^2+(ballB-ballA)*(∑ c,m (some c)^2)+
      2*ballB*m none*(∑ c,m (some c))+ballC*m none^2 := by
  simp only [Fintype.sum_option,Fin.sum_univ_four,ballBase]
  norm_num [Fin.ext_iff]
  ring

namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def mainEntropy (P : FiniteProgram α β) (z : Word β) : ℝ :=
  ∑ c, regionCost P.mass (P.density c) (P.part c (z c)) (P.part c (z c))

lemma mainEntropy_le (P : FiniteProgram α β) (z : Word β) (ht : P.bound ≤ threshold) :
    P.mainEntropy z ≤ 4*threshold := by
  calc
    _ ≤ ∑ c : Fin 4, threshold := sum_le_sum (fun c _ => (P.entropy_le c (z c)).trans ht)
    _ = _ := by norm_num

lemma mainEntropy_eq (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) :
    P.mainEntropy z = ∑ i, ∑ j, P.mass i*P.mass j*P.mainCost z i j := by
  simp only [mainEntropy,regionCost,part,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [mainCost,ballAllowed,sum_filter,mul_sum]
  apply sum_congr rfl
  intro c _
  simp only [P.ballClass_ne_some z hball i c,P.ballClass_ne_some z hball j c]
  split_ifs <;> simp_all

lemma mainEntropy_lower (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (ht : P.bound ≤ threshold) :
    (∑ u,∑ v, P.classMass z u*P.classMass z v*ballBase u v)-
      ballK*(∑ c,P.classMass z (some c)) ≤ P.mainEntropy z := by
  let corr := fun i : α => if P.ballClass z i=none then 0 else capacityG threshold (P.mass i)
  have hp (i j : α) :
      P.mass i*P.mass j*ballBase (P.ballClass z i) (P.ballClass z j)-
        (if i=j then corr i else 0) ≤ P.mass i*P.mass j*P.mainCost z i j := by
    by_cases hij : i=j
    · subst j
      cases hi : P.ballClass z i with
      | none =>
        have hh := mul_le_mul_of_nonneg_left (P.mainCost_base z hball hinj i i (Or.inr hi))
          (mul_nonneg (P.mass_nonneg i) (P.mass_nonneg i))
        simpa only [corr,hi,if_pos rfl,ite_true,sub_zero] using hh
      | some c =>
        simpa only [corr,hi,Option.some_ne_none,if_false,ite_false,ballBase,if_pos rfl,ite_true,pow_two] using P.mainCost_diagonal z hball hinj ht i c hi
    · have hh := mul_le_mul_of_nonneg_left (P.mainCost_base z hball hinj i j (Or.inl hij))
        (mul_nonneg (P.mass_nonneg i) (P.mass_nonneg j))
      simpa [hij] using hh
  have hsum := sum_le_sum (fun i (_ : i∈(univ : Finset α)) => sum_le_sum (fun j (_ : j∈(univ : Finset α)) => hp i j))
  simp only [sum_sub_distrib] at hsum
  rw [sum_group_pairs,← P.mainEntropy_eq z hball] at hsum
  have hd (i : α) : (∑ j, if i=j then corr i else 0)=corr i := by simp
  simp_rw [hd] at hsum
  change (∑ u,∑ v,P.classMass z u*P.classMass z v*ballBase u v)-∑ i,corr i ≤ _ at hsum
  have hc : (∑ i,corr i) ≤ ballK*(∑ c,P.classMass z (some c)) := by
    have hh : ∀ i, corr i ≤ if P.ballClass z i=none then 0 else ballK*P.mass i := by
      intro i
      dsimp [corr]
      split_ifs
      · rfl
      · exact capacityG_bound (by norm_num) (P.mass_nonneg i)
    apply (sum_le_sum (fun i _ => hh i)).trans
    have he := sum_group_weighted P.mass (P.ballClass z)
      (fun u => if u=none then 0 else ballK)
    have hf : (∑ i, if P.ballClass z i=none then 0 else ballK*P.mass i) =
      ∑ i, P.mass i*(if P.ballClass z i=none then 0 else ballK) := by
      apply sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [hf,he]
    simp [Fintype.sum_option,classMass,← mul_sum,mul_comm]
  linarith

lemma ball_has_large_arm (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (ht : P.bound ≤ threshold) : ∃ c, (33/50 : ℝ)<P.classMass z (some c) := by
  apply ball_large_arm (P.classMass_nonneg z none) (fun c => P.classMass_nonneg z (some c))
    (P.classMass_sum z)
  have hh := (P.mainEntropy_lower z hball hinj ht).trans (P.mainEntropy_le z ht)
  rwa [ballBase_sum] at hh

end FiniteProgram
end HadwigerRamsey4Col
