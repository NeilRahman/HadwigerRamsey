import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

namespace HadwigerRamsey4Col

abbrev Word (α : Type*) := Fin 4 → α

def Near {α : Type*} (x y : Word α) : Prop :=
  (x 0 = y 0 ∧ x 1 = y 1) ∨ (x 0 = y 0 ∧ x 2 = y 2) ∨
  (x 0 = y 0 ∧ x 3 = y 3) ∨ (x 1 = y 1 ∧ x 2 = y 2) ∨
  (x 1 = y 1 ∧ x 3 = y 3) ∨ (x 2 = y 2 ∧ x 3 = y 3)

def BallNear {α : Type*} (x y : Word α) : Prop :=
  (x 1 = y 1 ∧ x 2 = y 2 ∧ x 3 = y 3) ∨
  (x 0 = y 0 ∧ x 2 = y 2 ∧ x 3 = y 3) ∨
  (x 0 = y 0 ∧ x 1 = y 1 ∧ x 3 = y 3) ∨
  (x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2)

lemma near_iff_hamming {α : Type*} [DecidableEq α] (x y : Word α) :
    Near x y ↔ hammingDist x y ≤ 2 := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one]
  unfold Near
  split_ifs <;> simp_all

lemma ballNear_iff_hamming {α : Type*} [DecidableEq α] (x y : Word α) :
    BallNear x y ↔ hammingDist x y ≤ 1 := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one]
  unfold BallNear
  split_ifs <;> simp_all

/-- The three diameter-two families, stated without choosing names for symbols. -/
def PatternFamily {α : Type*} (S : Set (Word α)) : Prop :=
  (∃ i j : Fin 4, i ≠ j ∧ ∃ a b : α, ∀ x ∈ S, x i = a ∧ x j = b) ∨
  (∃ z : Word α, ∀ x ∈ S, BallNear x z) ∨
  (∃ σ : Fin 4 → Fin 4, Function.Bijective σ ∧
    ∃ a b c d e f g : α, a ≠ b ∧ c ≠ d ∧ e ≠ f ∧
    ∀ x ∈ S, (x ∘ σ) = ![a,c,e,g] ∨ (x ∘ σ) = ![a,d,f,g] ∨
      (x ∘ σ) = ![b,c,f,g] ∨ (x ∘ σ) = ![b,d,e,g])



lemma near_three {α : Type*} (a b c d e f g : α)
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (x : Word α)
    (h0 : Near x ![a,c,e,g]) (h1 : Near x ![b,d,e,g])
    (h2 : Near x ![b,c,f,g]) :
    BallNear x ![b,c,e,g] ∨ x = ![a,d,f,g] := by
  simp only [Near, BallNear, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at *
  have hext : (x = ![a,d,f,g]) ↔
      x 0 = a ∧ x 1 = d ∧ x 2 = f ∧ x 3 = g := by
    simp [funext_iff, Fin.forall_fin_succ]
  rw [hext]
  grind

lemma near_four {α : Type*} (a b c d e f g : α)
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (x : Word α)
    (h0 : Near x ![a,c,e,g]) (h1 : Near x ![b,d,e,g])
    (h2 : Near x ![b,c,f,g]) (h3 : Near x ![a,d,f,g]) :
    x = ![a,c,e,g] ∨ x = ![b,d,e,g] ∨ x = ![b,c,f,g] ∨ x = ![a,d,f,g] := by
  simp only [Near, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at *
  simp [funext_iff, Fin.forall_fin_succ]
  grind

lemma outside_pair {α : Type*} (a b c d e g : α)
    (hab : a ≠ b) (hcd : c ≠ d) (x : Word α)
    (h0 : Near x ![a,c,e,g]) (h1 : Near x ![b,d,e,g])
    (hx : x 2 ≠ e ∨ x 3 ≠ g) :
    (x = ![b,c,x 2,g] ∧ x 2 ≠ e) ∨
    (x = ![a,d,x 2,g] ∧ x 2 ≠ e) ∨
    (x = ![b,c,e,x 3] ∧ x 3 ≠ g) ∨
    (x = ![a,d,e,x 3] ∧ x 3 ≠ g) := by
  simp only [Near, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at *
  simp [funext_iff, Fin.forall_fin_succ]
  grind



lemma hamming_reindex {α : Type*} [DecidableEq α]
    (x y : Word α) (σ : Equiv.Perm (Fin 4)) :
    hammingDist (x ∘ σ) (y ∘ σ) = hammingDist x y := by
  unfold hammingDist
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    simpa using hi
  · intro i hi j hj hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ.symm j, ?_, by simp⟩
    simpa using hj

lemma near_reindex {α : Type*} (x y : Word α) (σ : Equiv.Perm (Fin 4)) :
    Near (x ∘ σ) (y ∘ σ) ↔ Near x y := by
  classical
  simp only [near_iff_hamming, hamming_reindex]

lemma pattern_descend {α : Type*} (S : Set (Word α)) (σ : Equiv.Perm (Fin 4))
    (h : PatternFamily ((fun x => x ∘ σ) '' S)) : PatternFamily S := by
  classical
  rcases h with ⟨i,j,hij,a,b,h⟩ | ⟨z,h⟩ | ⟨τ,hτ,a,b,c,d,e,f,g,hab,hcd,hef,h⟩
  · exact Or.inl ⟨σ i,σ j,σ.injective.ne hij,a,b,fun x hx => h _ ⟨x,hx,rfl⟩⟩
  · apply Or.inr ∘ Or.inl
    refine ⟨z ∘ σ.symm,fun x hx => ?_⟩
    have hh := h _ ⟨x,hx,rfl⟩
    rw [ballNear_iff_hamming] at hh ⊢
    have he : (z ∘ σ.symm) ∘ σ = z := by ext i; simp
    rw [← hamming_reindex x (z ∘ σ.symm) σ, he]
    exact hh
  · apply Or.inr ∘ Or.inr
    refine ⟨σ ∘ τ,σ.bijective.comp hτ,a,b,c,d,e,f,g,hab,hcd,hef,?_⟩
    exact fun x hx => h _ ⟨x,hx,rfl⟩

lemma pattern_of_triple {α : Type*} (S : Set (Word α))
    (hS : ∀ x ∈ S, ∀ y ∈ S, Near x y)
    (a b c d e f g : α) (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f)
    (h0 : ![a,c,e,g] ∈ S) (h1 : ![b,d,e,g] ∈ S) (h2 : ![b,c,f,g] ∈ S) :
    PatternFamily S := by
  classical
  by_cases h3 : ![a,d,f,g] ∈ S
  · apply Or.inr ∘ Or.inr
    refine ⟨id,Function.bijective_id,a,b,c,d,e,f,g,hab,hcd,hef,?_⟩
    intro x hx
    have hh := near_four a b c d e f g hab hcd hef x
      (hS x hx _ h0) (hS x hx _ h1) (hS x hx _ h2) (hS x hx _ h3)
    simp only [Function.comp_id]
    tauto
  · apply Or.inr ∘ Or.inl
    refine ⟨![b,c,e,g],fun x hx => ?_⟩
    rcases near_three a b c d e f g hab hcd hef x
      (hS x hx _ h0) (hS x hx _ h1) (hS x hx _ h2) with hh | hh
    · exact hh
    · exact (h3 (hh ▸ hx)).elim

lemma orient_pair {α : Type*} (x y : Word α) (h : Near x y)
    (hn : ¬BallNear x y) :
    ∃ σ : Equiv.Perm (Fin 4), x (σ 0) ≠ y (σ 0) ∧ x (σ 1) ≠ y (σ 1) ∧
      x (σ 2) = y (σ 2) ∧ x (σ 3) = y (σ 3) := by
  have hh :
      (x 0 ≠ y 0 ∧ x 1 ≠ y 1 ∧ x 2 = y 2 ∧ x 3 = y 3) ∨
      (x 0 ≠ y 0 ∧ x 2 ≠ y 2 ∧ x 1 = y 1 ∧ x 3 = y 3) ∨
      (x 0 ≠ y 0 ∧ x 3 ≠ y 3 ∧ x 1 = y 1 ∧ x 2 = y 2) ∨
      (x 1 ≠ y 1 ∧ x 2 ≠ y 2 ∧ x 0 = y 0 ∧ x 3 = y 3) ∨
      (x 1 ≠ y 1 ∧ x 3 ≠ y 3 ∧ x 0 = y 0 ∧ x 2 = y 2) ∨
      (x 2 ≠ y 2 ∧ x 3 ≠ y 3 ∧ x 0 = y 0 ∧ x 1 = y 1) := by
    unfold Near BallNear at *
    grind
  rcases hh with hh | hh | hh | hh | hh | hh
  · exact ⟨Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide), hh⟩
  · exact ⟨Equiv.ofBijective (![0,2,1,3] : Fin 4 → Fin 4) (by decide), hh⟩
  · exact ⟨Equiv.ofBijective (![0,3,1,2] : Fin 4 → Fin 4) (by decide), hh⟩
  · exact ⟨Equiv.ofBijective (![1,2,0,3] : Fin 4 → Fin 4) (by decide), hh⟩
  · exact ⟨Equiv.ofBijective (![1,3,0,2] : Fin 4 → Fin 4) (by decide), hh⟩
  · exact ⟨Equiv.ofBijective (![2,3,0,1] : Fin 4 → Fin 4) (by decide), hh⟩



lemma pattern_of_pair {α : Type*} (S : Set (Word α))
    (hS : ∀ x ∈ S, ∀ y ∈ S, Near x y)
    (a b c d e g : α) (hab : a ≠ b) (hcd : c ≠ d)
    (h0 : ![a,c,e,g] ∈ S) (h1 : ![b,d,e,g] ∈ S) : PatternFamily S := by
  classical
  by_cases hf : ∀ x ∈ S, x 2 = e ∧ x 3 = g
  · exact Or.inl ⟨2,3,by decide,e,g,hf⟩
  push Not at hf
  obtain ⟨x,hx,hout⟩ := hf
  have hout' : x 2 ≠ e ∨ x 3 ≠ g := by tauto
  rcases outside_pair a b c d e g hab hcd x (hS x hx _ h0) (hS x hx _ h1) hout'
    with ⟨he,hn⟩ | ⟨he,hn⟩ | ⟨he,hn⟩ | ⟨he,hn⟩
  · exact pattern_of_triple S hS a b c d e (x 2) g hab hcd (Ne.symm hn) h0 h1 (he ▸ hx)
  · let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective (![1 ,0 ,2 ,3] : Fin 4 → Fin 4) (by decide)
    apply pattern_descend S σ
    refine pattern_of_triple ((fun y => y ∘ σ) '' S) ?_ c d a b e (x 2) g hcd hab (Ne.symm hn) ?_ ?_ ?_
    · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
      exact (near_reindex u v σ).mpr (hS u hu v hv)
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) h0 using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) h1 using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) (he ▸ hx) using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
  · let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective (![0 ,1 ,3 ,2] : Fin 4 → Fin 4) (by decide)
    apply pattern_descend S σ
    refine pattern_of_triple ((fun y => y ∘ σ) '' S) ?_ a b c d g (x 3) e hab hcd (Ne.symm hn) ?_ ?_ ?_
    · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
      exact (near_reindex u v σ).mpr (hS u hu v hv)
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) h0 using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) h1 using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) (he ▸ hx) using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
  · let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective (![1 ,0 ,3 ,2] : Fin 4 → Fin 4) (by decide)
    apply pattern_descend S σ
    refine pattern_of_triple ((fun y => y ∘ σ) '' S) ?_ c d a b g (x 3) e hcd hab (Ne.symm hn) ?_ ?_ ?_
    · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
      exact (near_reindex u v σ).mpr (hS u hu v hv)
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) h0 using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) h1 using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]
    · convert Set.mem_image_of_mem (fun y => y ∘ σ) (he ▸ hx) using 1 <;>
        simp [σ, Function.comp_def, funext_iff, Fin.forall_fin_succ]

/-- Lemma 2: every diameter-two family of four-coordinate words is contained
in a two-fixed-coordinate family, a radius-one ball, or a relabelled triangle. -/
theorem lemma2 {α : Type*} [Nonempty α] [DecidableEq α] (S : Set (Word α))
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, hammingDist x y ≤ 2) : PatternFamily S := by
  classical
  have hS : ∀ x ∈ S, ∀ y ∈ S, Near x y :=
    fun x hx y hy => (near_iff_hamming x y).mpr (hdiam x hx y hy)
  by_cases hempty : S.Nonempty
  · obtain ⟨x,hx⟩ := hempty
    by_cases hball : ∀ y ∈ S, BallNear y x
    · exact Or.inr (Or.inl ⟨x,hball⟩)
    push Not at hball
    obtain ⟨y,hy,hn⟩ := hball
    obtain ⟨σ,h0,h1,h2,h3⟩ := orient_pair y x (hS y hy x hx) hn
    apply pattern_descend S σ
    refine pattern_of_pair ((fun z => z ∘ σ) '' S) ?_
      (x (σ 0)) (y (σ 0)) (x (σ 1)) (y (σ 1)) (x (σ 2)) (x (σ 3))
      (Ne.symm h0) (Ne.symm h1) ?_ ?_
    · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
      exact (near_reindex u v σ).mpr (hS u hu v hv)
    · convert Set.mem_image_of_mem (fun z => z ∘ σ) hx using 1
      simp [Function.comp_def, funext_iff, Fin.forall_fin_succ]
    · convert Set.mem_image_of_mem (fun z => z ∘ σ) hy using 1
      simp [Function.comp_def, funext_iff, Fin.forall_fin_succ, h2, h3]
  · exact Or.inr (Or.inl ⟨fun _ => Classical.arbitrary α, by simp [Set.not_nonempty_iff_eq_empty.mp hempty]⟩)

end HadwigerRamsey4Col
