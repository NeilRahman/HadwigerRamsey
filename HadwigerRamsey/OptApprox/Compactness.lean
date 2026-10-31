import HadwigerRamsey.OptApprox.Reduction

open scoped BigOperators
open Finset Real Set

namespace HadwigerRamsey.OptApprox
open Optimization
set_option maxHeartbeats 1000000

/-- A compact box containing the closed probability data and weights. -/
abbrev Config (k : ℕ) (ζ : ℝ) :=
  (Fin k → Icc (0 : ℝ) 1) × (Fin k → Icc (0 : ℝ) (1-ζ)) ×
    (Fin k → Fin k → Icc (0 : ℝ) (1-ζ)) × (Fin k → Fin k → Icc (0 : ℝ) (1-ζ))

def weights {k ζ} (x : Config k ζ) (i : Fin k) : ℝ := x.1 i
def prob {k ζ} (x : Config k ζ) (i : Fin k) : ℝ := x.2.1 i
def blue {k ζ} (x : Config k ζ) (i j : Fin k) : ℝ := x.2.2.1 i j
def green {k ζ} (x : Config k ζ) (i j : Fin k) : ℝ := x.2.2.2 i j

noncomputable def diagonalScore {k ζ} (x : Config k ζ) (i : Fin k) : ℝ :=
  weights x i * sqrt (logCost (prob x i))

lemma continuous_probability_cost {ζ : ℝ} (hζ : 0 < ζ) :
    Continuous (fun p : Icc (0 : ℝ) (1-ζ) => logCost (p : ℝ)) := by
  unfold logCost
  exact ((continuous_const.sub continuous_subtype_val).log (fun p => by
    have := p.property.2
    exact ne_of_gt (by linarith : 0 < 1-(p : ℝ)))).neg

lemma continuous_diagonalScore {k ζ} (hζ : 0 < ζ) (i : Fin k) :
    Continuous (fun x : Config k ζ => diagonalScore x i) := by
  have hc : Continuous (fun x : Config k ζ => logCost (prob x i)) :=
    (continuous_probability_cost hζ).comp (by fun_prop)
  exact (by unfold weights; fun_prop : Continuous (fun x : Config k ζ => weights x i)).mul hc.sqrt

lemma continuous_energy {k ζ} (hζ : 0 < ζ)
    (q : Config k ζ → Fin k → Fin k → Icc (0 : ℝ) (1-ζ))
    (hq : ∀ i j, Continuous (fun x => q x i j)) :
    Continuous (fun x => energy (weights x) (fun i j => q x i j)) := by
  unfold energy
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  exact ((by unfold weights; fun_prop : Continuous (fun x : Config k ζ => weights x i)).mul
    (by unfold weights; fun_prop : Continuous (fun x : Config k ζ => weights x j))).mul
    ((continuous_probability_cost hζ).comp (hq i j))

/-- The closed set of normalized data for which all three outcomes have a fixed gap. -/
def Bad (k : ℕ) (ζ : ℝ) : Set (Config k ζ) := {x |
  (∑ i, weights x i) = 1 ∧
  (∀ i, diagonalScore x i ≤ beta-ζ) ∧
  sqrt (energy (weights x) (blue x)) ≤ beta-ζ ∧
  sqrt (energy (weights x) (green x)) ≤ beta-ζ}

lemma isCompact_bad (k : ℕ) {ζ : ℝ} (hζ : 0 < ζ) : IsCompact (Bad k ζ) := by
  have hB : Continuous (fun x : Config k ζ => energy (weights x) (blue x)) :=
    continuous_energy hζ (fun x i j => x.2.2.1 i j) (fun i j => by fun_prop)
  have hG : Continuous (fun x : Config k ζ => energy (weights x) (green x)) :=
    continuous_energy hζ (fun x i j => x.2.2.2 i j) (fun i j => by fun_prop)
  apply IsClosed.isCompact
  simp only [Bad,setOf_and,setOf_forall]
  exact (isClosed_eq (by unfold weights; fun_prop) continuous_const).inter
    ((isClosed_iInter (fun i => isClosed_le (continuous_diagonalScore hζ i) continuous_const)).inter
      ((isClosed_le hB.sqrt continuous_const).inter (isClosed_le hG.sqrt continuous_const)))

/-- Total positive deficit in the diagonal and off-diagonal mass constraints. -/
noncomputable def defect {k ζ} (x : Config k ζ) : ℝ :=
  (∑ i, max (1-(prob x i+blue x i i+green x i i)) 0) +
  ∑ i, ∑ j, if i = j then 0 else max (1-(blue x i j+green x i j)) 0

lemma continuous_defect (k : ℕ) (ζ : ℝ) : Continuous (@defect k ζ) := by
  classical
  unfold defect prob blue green
  apply Continuous.add
  · apply continuous_finset_sum; intro i hi; fun_prop
  · apply continuous_finset_sum; intro i hi
    apply continuous_finset_sum; intro j hj
    split_ifs <;> fun_prop

lemma defect_nonneg {k ζ} (x : Config k ζ) : 0 ≤ defect x := by
  unfold defect
  exact add_nonneg (sum_nonneg (fun _ _ => le_max_right _ _))
    (sum_nonneg (fun _ _ => sum_nonneg (fun i _ => by split_ifs <;> positivity)))

lemma masses_of_defect_nonpos {k ζ} (x : Config k ζ) (hx : defect x ≤ 0) :
    (∀ i, 1 ≤ prob x i+blue x i i+green x i i) ∧
    (∀ i j, i ≠ j → 1 ≤ blue x i j+green x i j) := by
  classical
  have hd0 : 0 ≤ ∑ i, max (1-(prob x i+blue x i i+green x i i)) 0 :=
    sum_nonneg (fun _ _ => le_max_right _ _)
  have ho0 : 0 ≤ ∑ i, ∑ j, if i = j then 0 else max (1-(blue x i j+green x i j)) 0 :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by split_ifs <;> positivity))
  constructor
  · intro i
    have hh := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin k))) =>
      le_max_right (1-(prob x j+blue x j j+green x j j)) 0) (mem_univ i)
    have := le_max_left (1-(prob x i+blue x i i+green x i i)) 0
    dsimp [defect] at hx
    linarith
  · intro i j hij
    have hi := single_le_sum (fun r (_ : r ∈ (univ : Finset (Fin k))) =>
      sum_nonneg (fun s (_ : s ∈ (univ : Finset (Fin k))) =>
        show (0 : ℝ) ≤ (if r = s then 0 else max (1-(blue x r s+green x r s)) 0) by
          split_ifs <;> positivity)) (mem_univ i)
    have hj := single_le_sum (fun s (_ : s ∈ (univ : Finset (Fin k))) =>
      show (0 : ℝ) ≤ (if i = s then 0 else max (1-(blue x i s+green x i s)) 0) by
        split_ifs <;> positivity) (mem_univ j)
    rw [if_neg hij] at hj
    have := le_max_left (1-(blue x i j+green x i j)) 0
    dsimp [defect] at hx
    linarith

lemma defect_pos_on_bad {k ζ} (hζ : 0 < ζ) {x : Config k ζ} (hx : x ∈ Bad k ζ) :
    0 < defect x := by
  by_contra hn
  obtain ⟨hd,ho⟩ := masses_of_defect_nonpos x (le_of_not_gt hn)
  have hh := opt_closed_from_opt k (weights x) (prob x) (blue x) (green x)
    (fun i => (x.1 i).property.1) hx.1
    (fun i => (x.2.1 i).property.1) (fun i => by change (x.2.1 i : ℝ) < 1; have := (x.2.1 i).property.2; linarith)
    (fun i j => (x.2.2.1 i j).property.1) (fun i j => by change (x.2.2.1 i j : ℝ) < 1; have := (x.2.2.1 i j).property.2; linarith)
    (fun i j => (x.2.2.2 i j).property.1) (fun i j => by change (x.2.2.2 i j : ℝ) < 1; have := (x.2.2.2 i j).property.2; linarith) hd ho
  rcases hh with ⟨i,hi⟩ | h | h
  · have := hx.2.1 i
    change weights x i * sqrt (logCost (prob x i)) ≤ beta-ζ at this
    linarith
  · linarith [hx.2.2.1]
  · linarith [hx.2.2.2]

/-- Approximate mass constraints bound the total deficit. -/
lemma defect_le {k ζ δ} (x : Config k ζ) (hδ : 0 ≤ δ)
    (hd : ∀ i, 1-δ ≤ prob x i+blue x i i+green x i i)
    (ho : ∀ i j, i ≠ j → 1-δ ≤ blue x i j+green x i j) :
    defect x ≤ ((k : ℝ)+(k : ℝ)^2)*δ := by
  classical
  have h1 : (∑ i, max (1-(prob x i+blue x i i+green x i i)) 0) ≤ (k : ℝ)*δ := by
    calc
      _ ≤ ∑ _i : Fin k, δ := sum_le_sum (fun i _ => max_le (by linarith [hd i]) hδ)
      _ = _ := by simp
  have h2 : (∑ i, ∑ j, if i = j then 0 else max (1-(blue x i j+green x i j)) 0) ≤
      (k : ℝ)^2*δ := by
    calc
      _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, δ := by
        apply sum_le_sum; intro i hi
        apply sum_le_sum; intro j hj
        split_ifs with hij
        · exact hδ
        · exact max_le (by linarith [ho i j hij]) hδ
      _ = _ := by simp; ring
  dsimp [defect]
  nlinarith only [h1,h2]

/-- A positive tolerance for one fixed dimension, obtained from a compact minimum. -/
theorem fixed_dimension (k : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Bad k ζ,
      ¬ ((∀ i, 1-δ ≤ prob x i+blue x i i+green x i i) ∧
         (∀ i j, i ≠ j → 1-δ ≤ blue x i j+green x i j)) := by
  classical
  by_cases hne : (Bad k ζ).Nonempty
  · obtain ⟨x,hx,hmin⟩ := (isCompact_bad k hζ).exists_isMinOn hne (continuous_defect k ζ).continuousOn
    have hp := defect_pos_on_bad hζ hx
    let C : ℝ := (k : ℝ)+(k : ℝ)^2
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let δ := defect x/(C+1)
    have hδ : 0 < δ := div_pos hp (by positivity)
    refine ⟨δ,hδ,?_⟩
    intro y hy ⟨hd,ho⟩
    have hymin : defect x ≤ defect y := hmin hy
    have hybound := defect_le y hδ.le hd ho
    have he : (C+1)*δ = defect x := by dsimp [δ]; field_simp
    change defect y ≤ C*δ at hybound
    nlinarith
  · exact ⟨1,by norm_num,fun x hx => False.elim (hne ⟨x,hx⟩)⟩

end HadwigerRamsey.OptApprox
