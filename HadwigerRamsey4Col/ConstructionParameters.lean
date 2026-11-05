import HadwigerRamsey4Col.ComponentProgram

open scoped BigOperators Classical

namespace HadwigerRamsey4Col.Construction

lemma exists_positive_lt_family {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : ∃ d : ℝ, 0 < d ∧ ∀ i, d < a i := by
  have h : ∀ s : Finset ι, ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d < a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨d, hd, hds⟩ := ih
      have hai := ha i
      refine ⟨min d (a i / 2), lt_min hd (by positivity), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt (by linarith [ha j])
      · exact (min_le_left _ _).trans_lt (hds j hj)
  obtain ⟨d, hd, hds⟩ := h Finset.univ
  exact ⟨d, hd, fun i => hds i (Finset.mem_univ i)⟩

/-- A single error parameter works for all densities and all components. -/
theorem exists_construction_parameter {r : ℕ} (hr : 2 ≤ r)
    (I : ComponentInstance r) {B : ℝ} (hB : I.objective < B) :
    ∃ d : ℝ, 0 < d ∧ (r * I.k : ℝ) * d < 1 ∧
      (∀ c i j, I.density c i j ≤ 1-d) ∧
      (∀ c t, 0 < I.energy c t → d < I.energy c t) ∧
      (1+d)*I.objective < B := by
  obtain ⟨a, ha, hpa⟩ := exists_positive_lt_family
    (fun x : Fin r × Fin I.k × Fin I.k => 1 - I.density x.1 x.2.1 x.2.2)
    (fun x => sub_pos.mpr (I.density_lt_one _ _ _))
  obtain ⟨b, hb, hpb⟩ := exists_positive_lt_family
    (fun x : Fin r × Fin I.k => if 0 < I.energy x.1 x.2 then I.energy x.1 x.2 else 1)
    (by intro x; split_ifs with h <;> positivity)
  have hM : 0 < I.objective := (beta_pos hr).trans_le (beta_le_objective hr I)
  let q : ℝ := r * I.k
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let d := min a (min b (min ((B-I.objective)/(2*I.objective)) (1/(2*(q+1)))))
  have hd : 0 < d := by dsimp [d]; positivity
  have hda : d ≤ a := min_le_left _ _
  have hdb : d ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hdM : d ≤ (B-I.objective)/(2*I.objective) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdq : d ≤ 1/(2*(q+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨d, hd, ?_, ?_, ?_, ?_⟩
  · have h := (le_div_iff₀ (show 0 < 2*(q+1) by positivity)).mp hdq
    change q*d < 1
    nlinarith
  · intro c i j
    have h := hda.trans_lt (hpa (c,i,j))
    dsimp at h
    linarith
  · intro c t hE
    have h := hdb.trans_lt (hpb (c,t))
    simpa only [if_pos hE] using h
  · have h := (le_div_iff₀ (show 0 < 2*I.objective by positivity)).mp hdM
    nlinarith

end HadwigerRamsey4Col.Construction
