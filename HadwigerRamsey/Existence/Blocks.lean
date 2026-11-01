import HadwigerRamsey.Existence.Sampling
import HadwigerRamsey.Existence.Constants
import HadwigerRamsey.Blocks

open scoped BigOperators Classical
open Finset Real
namespace HadwigerRamsey.Existence

def halfMap (m : ℕ) (i : Fin 2) (v : Fin m) : Fin (2*m) := ⟨i.val*m+v.val,by nlinarith [i.isLt,v.isLt]⟩
lemma halfMap_strict (m : ℕ) (i : Fin 2) : StrictMono (halfMap m i) := by
  intro u v huv; change i.val*m+u.val < i.val*m+v.val; exact Nat.add_lt_add_left huv _
def halfClass {m : ℕ} (v : Fin (2*m)) : Fin 2 := if v.val < m then 0 else 1
lemma halfClass_map (m : ℕ) (i : Fin 2) (v : Fin m) : halfClass (halfMap m i v) = i := by
  fin_cases i <;> simp [halfClass,halfMap] <;> omega
lemma halfMap_cover (m : ℕ) (i : Fin 2) (v : Fin (2*m)) (h : halfClass v = i) : v ∈ Set.range (halfMap m i) := by
  fin_cases i
  · have hv : v.val < m := by simpa [halfClass] using h
    exact ⟨⟨v.val,hv⟩,by apply Fin.ext; simp [halfMap]⟩
  · have hv : m ≤ v.val := by simpa [halfClass] using h
    refine ⟨⟨v.val-m,by omega⟩,?_⟩
    apply Fin.ext; simp only [halfMap,Fin.val_one,Nat.one_mul]; omega
lemma half_mass {m : ℕ} (hm : 0 < m) (i : Fin 2) : classMass (halfClass (m := m)) i = 1/2 := by
  have he : (univ.filter (fun v : Fin (2*m) => halfClass v = i)) = univ.image (halfMap m i) := by
    ext v
    simp only [mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro hv; obtain ⟨u,rfl⟩ := halfMap_cover m i v hv; exact ⟨u,rfl⟩
    · rintro ⟨u,rfl⟩; exact halfClass_map m i u
  unfold classMass
  rw [he,card_image_of_injective _ (halfMap_strict m i).injective]
  simp only [card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
noncomputable def rate (m : ℕ) (e : Edge (2*m)) : ℝ := if halfClass e.val.1 = halfClass e.val.2 then p else 1/2
lemma rate_nonneg (m : ℕ) (e : Edge (2*m)) : 0 ≤ rate m e := by unfold rate; split_ifs <;> linarith [p_bounds.1]
lemma rate_half (m : ℕ) (e : Edge (2*m)) : rate m e ≤ 1/2 := by unfold rate; split_ifs <;> linarith [p_bounds.2]
noncomputable def mixed (i j : Fin 2) : ℝ := if i=j then p else 1/2
lemma mixed_symmetric : ∀ i j, mixed i j = mixed j i := by intros; simp [mixed,eq_comm]
lemma mixed_nonneg : ∀ i j, 0 ≤ mixed i j := by intros; unfold mixed; split_ifs <;> linarith [p_bounds.1]
lemma mixed_entropy {m : ℕ} (hm : 0 < m) : blockLambda (halfClass (m := m)) mixed = beta^2 := by
  unfold blockLambda
  simp only [half_mass hm]
  simp [Fin.sum_univ_two,mixed]
  norm_num
  convert entropy_mixed using 1 <;> ring
end HadwigerRamsey.Existence
