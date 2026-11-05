import HadwigerRamsey4Col.BallGeometry
import HadwigerRamsey4Col.ComponentCapacity

open Real Finset
open scoped BigOperators Classical
namespace HadwigerRamsey4Col

lemma cost_sum_lower {δ : Type} [DecidableEq δ] (S : Finset δ) (q : δ → ℝ) (r : ℝ)
    (hq : ∀ c ∈ S, q c < 1) (hr : r < 1) (hs : (S.card : ℝ)*r ≤ ∑ c ∈ S, q c) :
    (S.card : ℝ)*cost r ≤ ∑ c ∈ S, cost (q c) := by
  have hh := sum_le_sum (fun c hc => cost_tangent (hq c hc) hr)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hh
  simp_rw [← sum_div, sum_sub_distrib, sum_const, nsmul_eq_mul] at hh
  have hd : 0 ≤ ((∑ c ∈ S, q c)-(S.card : ℝ)*r)/(1-r) :=
    div_nonneg (sub_nonneg.mpr hs) (sub_pos.mpr hr).le
  linarith

noncomputable def ballAllowed (u v : Option (Fin 4)) : Finset (Fin 4) :=
  univ.filter (fun c => u ≠ some c ∧ v ≠ some c)

noncomputable def ballBase (u v : Option (Fin 4)) : ℝ :=
  match u,v with
  | none,none => ballC
  | some c,some d => if c=d then ballB else ballA
  | _,_ => ballB

lemma ballAllowed_nonempty (u v : Option (Fin 4)) : (ballAllowed u v).Nonempty := by
  cases u with
  | none => cases v with
    | none => exact ⟨0, by simp [ballAllowed]⟩
    | some d => fin_cases d <;> decide
  | some c => cases v with
    | none => fin_cases c <;> decide
    | some d => fin_cases c <;> fin_cases d <;> decide

lemma ballBase_eq (u v : Option (Fin 4)) :
    ballBase u v = ((ballAllowed u v).card : ℝ)*cost (1/((ballAllowed u v).card : ℝ)) := by
  have h2 : cost (1/2:ℝ)=log 2 := by dsimp [cost]; rw [← log_inv]; norm_num
  have h4 : cost (1/4:ℝ)=log (4/3) := by dsimp [cost]; rw [← log_inv]; norm_num
  have hi2 : cost ((2:ℝ)⁻¹)=log 2 := by simpa using h2
  have hi3 : cost ((3:ℝ)⁻¹)=log (3/2) := by simpa using cost_third
  have hi4 : cost ((4:ℝ)⁻¹)=log (4/3) := by simpa using h4
  have hc : (ballAllowed u v).card =
      if u=none ∧ v=none then 4 else if u=v ∨ u=none ∨ v=none then 3 else 2 := by
    cases u with
    | none => cases v with
      | none => decide
      | some d => fin_cases d <;> decide
    | some c => cases v with
      | none => fin_cases c <;> decide
      | some d => fin_cases c <;> fin_cases d <;> decide
  rw [hc]
  cases u with
  | none => cases v with
    | none => norm_num [ballBase,ballC,h4,hi4]
    | some d => simp [ballBase,ballB,hi3,Option.some_ne_none]
  | some c => cases v with
    | none => simp [ballBase,ballB,hi3,Option.some_ne_none]
    | some d => by_cases h:c=d <;> simp [ballBase,h,ballA,ballB,cost_third,h2,hi2,hi3]

namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def mainCost (P : FiniteProgram α β) (z : Word β) (i j : α) : ℝ :=
  ∑ c ∈ ballAllowed (P.ballClass z i) (P.ballClass z j), cost (P.density c i j)

lemma allowed_density_sum (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (i j : α) (hij : i ≠ j ∨ P.ballClass z i=none) :
    ∑ c ∈ ballAllowed (P.ballClass z i) (P.ballClass z j), P.density c i j = 1 := by
  rw [← P.density_sum i j]
  apply sum_subset (filter_subset _ _)
  intro c _ hc
  have hn : P.ballClass z i=some c ∨ P.ballClass z j=some c := by
    simp only [ballAllowed, mem_filter, mem_univ, true_and] at hc
    tauto
  rcases hij with hij | hi
  · exact P.ball_nonmain_zero z hball hinj i j hij c hn
  · by_cases he : i=j
    · subst j
      simp [hi] at hn
    · exact P.ball_nonmain_zero z hball hinj i j he c hn

lemma mainCost_base (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (i j : α) (hij : i ≠ j ∨ P.ballClass z i=none) :
    ballBase (P.ballClass z i) (P.ballClass z j) ≤ P.mainCost z i j := by
  let S := ballAllowed (P.ballClass z i) (P.ballClass z j)
  have hn : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr (ballAllowed_nonempty _ _)
  have htwo : 1 < S.card := by
    dsimp [S]
    cases hu : P.ballClass z i with
    | none => cases hv : P.ballClass z j with
      | none => decide
      | some d => fin_cases d <;> decide
    | some c => cases hv : P.ballClass z j with
      | none => fin_cases c <;> decide
      | some d => fin_cases c <;> fin_cases d <;> decide
  have hr : 1/(S.card : ℝ)<1 := (div_lt_one hn).mpr (by exact_mod_cast htwo)
  rw [ballBase_eq]
  apply cost_sum_lower _ _ _ (fun c _ => P.density_lt_one c i j) hr
  rw [P.allowed_density_sum z hball hinj i j hij]
  dsimp [S]
  rw [mul_one_div_cancel (ne_of_gt hn)]

lemma singleton_density_capacity (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (ht : P.bound ≤ threshold) (i : α) (c : Fin 4) (hi : P.ballClass z i=some c) :
    P.mass i^2*P.density c i i ≤ capacityF threshold (P.mass i) := by
  have hh := P.region_capacity c {i} (show regionCost P.mass (P.density c) {i} {i} ≤ threshold by
    have he := (P.entropy_le c (P.label c i)).trans ht
    change regionCost P.mass (P.density c) (P.part c (P.label c i)) (P.part c (P.label c i)) ≤ threshold at he
    rwa [P.ball_singleton_part z hball hinj i c hi] at he)
  simpa [regionDensity,regionMass,pow_two] using hh

lemma mainCost_diagonal (P : FiniteProgram α β) (z : Word β)
    (hball : ∀ i, BallNear (P.word i) z) (hinj : Function.Injective P.word)
    (ht : P.bound ≤ threshold) (i : α) (c : Fin 4) (hi : P.ballClass z i=some c) :
    P.mass i^2*ballB-capacityG threshold (P.mass i) ≤ P.mass i^2*P.mainCost z i i := by
  let e := exp (-(threshold/P.mass i^2))
  have he0 : 0<e := exp_pos _
  have he1 : e≤1 := exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (by norm_num : (0:ℝ)≤threshold) (sq_nonneg _)))
  have hd := P.singleton_density_capacity z hball hinj ht i c hi
  have hd' : P.density c i i ≤ 1-e := by
    dsimp [capacityF] at hd
    nlinarith [sq_pos_of_pos (P.mass_pos i)]
  have hcard : (ballAllowed (some c) (some c)).card=3 := by fin_cases c <;> decide
  have hsum : ∑ d ∈ ballAllowed (some c) (some c), P.density d i i = 1-P.density c i i := by
    have he : ballAllowed (some c) (some c)=univ.erase c := by ext d; simp [ballAllowed,ne_comm]
    rw [he, sum_erase_eq_sub (mem_univ c), P.density_sum]
  have hh := cost_sum_lower (ballAllowed (some c) (some c)) (fun d => P.density d i i) (e/3)
    (fun d _ => P.density_lt_one d i i) (by linarith)
    (by rw [hcard,hsum]; norm_num; linarith)
  have hlog : 3*cost (e/3) = ballB-3*log ((3-e)/2) := by
    have hx : 1-e/3 = (2/3 : ℝ)*((3-e)/2) := by ring
    dsimp [cost,ballB]
    rw [hx, log_mul (by norm_num) (by linarith : (3-e)/2 ≠ 0)]
    have hl : log (2/3 : ℝ)= -log (3/2 : ℝ) := by rw [← log_inv]; norm_num
    rw [hl]
    ring
  rw [hcard] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [hlog] at hh
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg (P.mass i))
  dsimp [mainCost]
  rw [hi]
  dsimp [capacityG,e] at *
  nlinarith

end FiniteProgram
end HadwigerRamsey4Col
