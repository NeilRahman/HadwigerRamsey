import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open scoped BigOperators Classical
open Finset

namespace ComponentTransfer.Realization

/-- Prescribing equality of two distinct coordinates removes at least one
free choice from a finite map. -/
lemma coordinate_collision_card_le {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    (univ.filter (fun f : ι → V => f i = f j)).card ≤
      Fintype.card V ^ (Fintype.card ι - 1) := by
  let restrict : {f : ι → V // f i = f j} → ({x : ι // x ≠ j} → V) :=
    fun f x => f.val x.val
  have hinj : Function.Injective restrict := by
    intro f g h
    apply Subtype.ext
    funext x
    by_cases hx : x = j
    · subst x
      calc
        f.val j = f.val i := f.property.symm
        _ = g.val i := congrFun h ⟨i,hij⟩
        _ = g.val j := g.property
    · exact congrFun h ⟨x,hx⟩
  have h := Fintype.card_le_of_injective restrict hinj
  have hc : Fintype.card {x : ι // x ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Fintype.card_fun, hc, Fintype.card_subtype] at h
  exact h

/-- A union bound for repeated vertices in maps from a finite test graph. -/
theorem noninjective_card_le (m n : ℕ) :
    (univ.filter (fun f : Fin m → Fin n => ¬ Function.Injective f)).card ≤
      m*m*n^(m-1) := by
  let B := fun ij : Fin m × Fin m =>
    if ij.1 ≠ ij.2 then univ.filter (fun f : Fin m → Fin n => f ij.1 = f ij.2) else ∅
  have hsub : univ.filter (fun f : Fin m → Fin n => ¬ Function.Injective f) ⊆
      univ.biUnion B := by
    intro f hf
    have hn := (mem_filter.mp hf).2
    have hn' : ∃ i j, f i = f j ∧ i ≠ j := by
      simpa only [Function.Injective, not_forall, Classical.not_imp, exists_prop] using hn
    obtain ⟨i,j,he,hij⟩ := hn'
    exact mem_biUnion.mpr ⟨(i,j),mem_univ _,by simpa [B,hij] using he⟩
  calc
    _ ≤ (univ.biUnion B).card := card_le_card hsub
    _ ≤ ∑ ij : Fin m × Fin m, (B ij).card := card_biUnion_le
    _ ≤ ∑ _ij : Fin m × Fin m, n^(m-1) := by
      apply sum_le_sum
      intro ij _
      dsimp only [B]
      split_ifs with hij
      · have h := coordinate_collision_card_le (V := Fin n) ij.1 ij.2 hij
        simp only [Fintype.card_fin] at h
        convert h using 1
        · rfl
        · apply congrArg Finset.card
          ext f
          simp
      · simp
    _ = _ := by simp [mul_assoc]

/-- An overlapping coordinate in a pair of maps removes one free choice. -/
lemma pair_coordinate_collision_card_le {m n : ℕ} (i j : Fin m) :
    (univ.filter (fun fg : (Fin m → Fin n) × (Fin m → Fin n) => fg.1 i = fg.2 j)).card ≤
      n^(2*m-1) := by
  let restrict : {fg : (Fin m → Fin n) × (Fin m → Fin n) // fg.1 i = fg.2 j} →
      (Fin m → Fin n) × ({x : Fin m // x ≠ j} → Fin n) :=
    fun fg => (fg.val.1, fun x => fg.val.2 x.val)
  have hinj : Function.Injective restrict := by
    intro f g h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Subtype.ext
    apply Prod.ext
    · exact h1
    · funext x
      by_cases hx : x = j
      · subst x
        calc
          f.val.2 j = f.val.1 i := f.property.symm
          _ = g.val.1 i := congrFun h1 i
          _ = g.val.2 j := g.property
      · exact congrFun h2 ⟨x,hx⟩
  have h := Fintype.card_le_of_injective restrict hinj
  have hc : Fintype.card {x : Fin m // x ≠ j} = m - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, hc,
    Fintype.card_fin, ← pow_add, Fintype.card_subtype] at h
  simp only [Fintype.card_fin] at h
  convert h using 1
  congr 1
  omega

/-- Pairs of maps with overlapping ranges are at most a fraction `m²/n`. -/
theorem overlap_card_le (m n : ℕ) :
    (univ.filter (fun fg : (Fin m → Fin n) × (Fin m → Fin n) =>
      ∃ i j, fg.1 i = fg.2 j)).card ≤ m*m*n^(2*m-1) := by
  let B := fun ij : Fin m × Fin m =>
    univ.filter (fun fg : (Fin m → Fin n) × (Fin m → Fin n) => fg.1 ij.1 = fg.2 ij.2)
  have hsub : univ.filter (fun fg : (Fin m → Fin n) × (Fin m → Fin n) =>
      ∃ i j, fg.1 i = fg.2 j) ⊆ univ.biUnion B := by
    intro fg hfg
    obtain ⟨i,j,hij⟩ := (mem_filter.mp hfg).2
    exact mem_biUnion.mpr ⟨(i,j),mem_univ _,mem_filter.mpr ⟨mem_univ _,hij⟩⟩
  calc
    _ ≤ (univ.biUnion B).card := card_le_card hsub
    _ ≤ ∑ ij : Fin m × Fin m, (B ij).card := card_biUnion_le
    _ ≤ ∑ _ij : Fin m × Fin m, n^(2*m-1) :=
      sum_le_sum (fun ij _ => pair_coordinate_collision_card_le ij.1 ij.2)
    _ = _ := by simp [mul_assoc]

lemma normalize_card_bound {C K n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : K ≤ C*n^(m-1)) : (K : ℝ)/(n : ℝ)^m ≤ (C : ℝ)/n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : (K : ℝ) ≤ C*(n : ℝ)^(m-1) := by exact_mod_cast h
  have hp : (n : ℝ)^m = (n : ℝ)^(m-1)*(n : ℝ) := by
    calc
      _ = (n : ℝ)^((m-1)+1) := by congr 1; omega
      _ = _ := pow_succ _ _
  calc
    _ ≤ ((C : ℝ)*(n : ℝ)^(m-1))/(n : ℝ)^m :=
      div_le_div_of_nonneg_right hR (by positivity)
    _ = _ := by rw [hp]; field_simp

/-- The fraction of maps with a repeated vertex is at most `m²/n`. -/
theorem noninjective_fraction_le (m n : ℕ) (hn : 0 < n) :
    ((univ.filter (fun f : Fin m → Fin n => ¬ Function.Injective f)).card : ℝ) /
      (n : ℝ)^m ≤ (m : ℝ)^2/n := by
  by_cases hm : m = 0
  · subst m
    have h := noninjective_card_le 0 n
    have hz : (univ.filter (fun f : Fin 0 → Fin n => ¬ Function.Injective f)).card = 0 :=
      Nat.eq_zero_of_le_zero (by simpa only [zero_mul] using h)
    rw [hz]
    norm_num
  · have h := normalize_card_bound hn (Nat.pos_of_ne_zero hm) (noninjective_card_le m n)
    simpa only [Nat.cast_mul, pow_two] using h

/-- The fraction of pairs of maps with overlapping ranges is at most `m²/n`. -/
theorem overlap_fraction_le (m n : ℕ) (hn : 0 < n) :
    ((univ.filter (fun fg : (Fin m → Fin n) × (Fin m → Fin n) =>
      ∃ i j, fg.1 i = fg.2 j)).card : ℝ) / ((n : ℝ)^m)^2 ≤ (m : ℝ)^2/n := by
  by_cases hm : m = 0
  · subst m
    have h := overlap_card_le 0 n
    have hz : (univ.filter (fun fg : (Fin 0 → Fin n) × (Fin 0 → Fin n) =>
        ∃ i j, fg.1 i = fg.2 j)).card = 0 := Nat.eq_zero_of_le_zero (by simpa only [zero_mul] using h)
    rw [hz]
    norm_num
  · have h := normalize_card_bound hn (show 0 < 2*m by omega) (overlap_card_le m n)
    simpa only [Nat.cast_mul, pow_mul, mul_comm 2 m, pow_two] using h

end ComponentTransfer.Realization
