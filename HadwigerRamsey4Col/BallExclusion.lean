import HadwigerRamsey4Col.BallAggregation

open Real Finset
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
namespace HadwigerRamsey4Col
namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def mainDensity (P : FiniteProgram α β) (z : Word β) : ℝ :=
  ∑ c, P.partDensity c (z c)
noncomputable def soloDensity (P : FiniteProgram α β) (z : Word β) (i : α) : ℝ :=
  match P.ballClass z i with
  | none => 0
  | some c => P.mass i^2*P.density c i i

lemma mainDensity_eq (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) :
    P.mainDensity z = ∑ i, ∑ j, P.mass i*P.mass j*
      (∑ c ∈ ballAllowed (P.ballClass z i) (P.ballClass z j), P.density c i j) := by
  simp only [mainDensity,partDensity,regionDensity,part,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [ballAllowed,sum_filter,mul_sum]
  apply sum_congr rfl
  intro c _
  simp only [P.ballClass_ne_some z hball i c,P.ballClass_ne_some z hball j c]
  split_ifs <;> simp_all

lemma ball_density_conservation (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word) :
    P.mainDensity z+∑ i,P.soloDensity z i=1 := by
  have hp (i j : α) : P.mass i*P.mass j*
      (∑ c ∈ ballAllowed (P.ballClass z i) (P.ballClass z j),P.density c i j)+
      (if i=j then P.soloDensity z i else 0)=P.mass i*P.mass j := by
    by_cases hij : i=j
    · subst j
      cases hi : P.ballClass z i with
      | none =>
        have hh := P.allowed_density_sum z hball hinj i i (Or.inr hi)
        rw [hi] at hh
        simp only [hh,soloDensity,hi,ite_true,mul_one,add_zero]
      | some c =>
        have he : ballAllowed (some c) (some c)=univ.erase c := by ext d; simp [ballAllowed,ne_comm]
        rw [he,sum_erase_eq_sub (mem_univ c),P.density_sum]
        simp [soloDensity,hi]
        ring
    · rw [P.allowed_density_sum z hball hinj i j (Or.inl hij)]
      simp [hij]
  have hh := sum_congr (s₁ := (univ : Finset α)) rfl (fun i _ =>
    sum_congr (s₁ := (univ : Finset α)) rfl (fun j _ => hp i j))
  simp only [sum_add_distrib] at hh
  have hd (i : α) : (∑ j, if i=j then P.soloDensity z i else 0)=P.soloDensity z i := by simp
  simp_rw [hd] at hh
  rw [← P.mainDensity_eq z hball,← sum_mul_sum,P.mass_sum,one_mul] at hh
  exact hh

lemma soloDensity_bound (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (ht : P.bound ≤ threshold) :
    (∑ i,P.soloDensity z i) ≤ (16/25 : ℝ)*sqrt threshold := by
  calc
    _ ≤ ∑ i, (16/25 : ℝ)*sqrt threshold*P.mass i := by
      apply sum_le_sum
      intro i _
      cases hi : P.ballClass z i with
      | none => simp only [soloDensity,hi]; have hm := P.mass_nonneg i; positivity
      | some c =>
        simpa only [soloDensity,hi] using (P.singleton_density_capacity z hball hinj ht i c hi).trans
          (capacityF_bound (by norm_num) (P.mass_nonneg i))
    _ = _ := by rw [← mul_sum,P.mass_sum,mul_one]

lemma mainDensity_bound (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (ht : P.bound ≤ threshold) :
    P.mainDensity z ≤ 3*capacityF threshold 1+capacityF threshold (17/50) := by
  obtain ⟨c,hc⟩ := P.ball_has_large_arm z hball hinj ht
  have hm : P.partMass c (z c) ≤ (17/50 : ℝ) := by rw [P.ball_main_mass z hball]; linarith
  calc
    _ ≤ ∑ d : Fin 4, if d=c then capacityF threshold (17/50) else capacityF threshold 1 := by
      apply sum_le_sum
      intro d _
      by_cases hd : d=c
      · subst d
        simp only [if_pos rfl]
        exact (P.part_capacity ht c (z c)).trans
          (capacityF_mono (by norm_num) (P.partMass_nonneg c (z c)) hm)
      · simp only [if_neg hd]
        exact (P.part_capacity ht d (z d)).trans
          (capacityF_mono (by norm_num) (P.partMass_nonneg d (z d)) (P.partMass_le_one d (z d)))
    _ = _ := by simp only [Fin.sum_univ_four]; fin_cases c <;> norm_num [Fin.ext_iff] <;> ring

/-- No instance with distinct label words and bound at most the rational threshold
can lie in a radius-one Hamming ball. -/
lemma no_ball (P : FiniteProgram α β) (ht : P.bound ≤ threshold)
    (hinj : Function.Injective P.word) (z : Word β) (hball : ∀ i,BallNear (P.word i) z) : False := by
  have h0 := P.ball_density_conservation z hball hinj
  have h1 := P.soloDensity_bound z hball hinj ht
  have h2 := P.mainDensity_bound z hball hinj ht
  have h3 := ball_capacity_sum_lt
  linarith

end FiniteProgram
end HadwigerRamsey4Col
