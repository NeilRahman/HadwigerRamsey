import HadwigerRamsey.Graph

open scoped BigOperators
open Finset
namespace HadwigerRamsey

lemma sum_edges_eq_triangle {n : ℕ} (w : Fin n → Fin n → ℝ) :
    ∑ e : Edge n, w e.val.1 e.val.2 = ∑ u, ∑ v, if u < v then w u v else 0 := by
  rw [← Finset.sum_subtype (univ.filter (fun e : Fin n × Fin n => e.1 < e.2))
    (by simp) (fun e => w e.1 e.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

/-- Lemma `lem:total-weight`, expressed using a sum over vertices. -/
theorem total_weight_identity {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, w u v = w v u) :
    2 * (∑ e : Edge n, w e.val.1 e.val.2) + ∑ u, w u u = ∑ u, ∑ v, w u v := by
  rw [sum_edges_eq_triangle]
  have hswap : (∑ u : Fin n, ∑ v : Fin n, if v < u then w u v else 0) =
      ∑ u : Fin n, ∑ v : Fin n, if u < v then w u v else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsym v u]
  have hsplit : (∑ u : Fin n, ∑ v : Fin n, w u v) =
      (∑ u, ∑ v, if u < v then w u v else 0) +
      (∑ u, ∑ v, if v < u then w u v else 0) + ∑ u, w u u := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have hdiag : (∑ v : Fin n, if v = u then w u v else 0) = w u u := by simp
    rw [← hdiag]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rcases lt_trichotomy u v with h | h | h <;> simp [ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt, *]
  rw [hswap] at hsplit
  linarith

lemma total_weight_le {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, w u v = w v u) (hw : ∀ u v, 0 ≤ w u v) :
    ∑ e : Edge n, w e.val.1 e.val.2 ≤ (∑ u, ∑ v, w u v) / 2 := by
  have := total_weight_identity w hsym
  have : 0 ≤ ∑ u, w u u := Finset.sum_nonneg (fun u _ => hw u u)
  linarith [total_weight_identity w hsym]

/-- Total weights of disjoint block pairs do not exceed total edge weight. -/
lemma sum_cross_weights_le {n s : ℕ} (f : Fin n → Fin s) (w : Edge n → ℝ)
    (hw : ∀ e, 0 ≤ w e) :
    (∑ a : Edge s, ∑ e ∈ univ.filter (Crosses f a), w e) ≤ ∑ e, w e := by
  classical
  rw [← Finset.sum_biUnion]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun e _ _ => hw e)
  · intro a ha b hb hab
    exact Finset.disjoint_left.mpr (fun e he he' =>
      Set.disjoint_left.mp (crosses_disjoint f hab) (mem_filter.mp he).2 (mem_filter.mp he').2)

lemma edge_card_real (n : ℕ) :
    (Fintype.card (Edge n) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
  have h := total_weight_identity (n := n) (fun _ _ => 1) (fun _ _ => rfl)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_fin] at h
  nlinarith

end HadwigerRamsey
