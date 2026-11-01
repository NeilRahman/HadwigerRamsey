import HadwigerRamsey.ThomasonUpper.NonneighborWeights

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- Sorting by a real weight, breaking ties by the vertex order, then
cutting the list into consecutive blocks of equal size. -/
theorem exists_sorted_block_enumeration {V : Type*} [LinearOrder V]
    (S : Finset V) (rho : V → ℝ) {ell s : ℕ} (hcard : S.card = ell*s) :
    ∃ e : Fin ell × Fin s ≃ S,
      ∀ a b : Fin ell, ∀ x y : Fin s,
        s*a.val+x.val ≤ s*b.val+y.val → rho (e (a,x)) ≤ rho (e (b,y)) := by
  classical
  let key : V → ℝ ×ₗ V := fun u => toLex (rho u,u)
  have hkey : Function.Injective key := by
    intro u v huv
    exact congrArg (fun z : ℝ ×ₗ V => (ofLex z).2) huv
  let T := S.image key
  let g : T ≃ S :=
    { toFun := fun z => ⟨(ofLex z.val).2, by
        obtain ⟨u,hu,huz⟩ := mem_image.mp z.property
        exact (congrArg (fun w : ℝ ×ₗ V => (ofLex w).2) huz) ▸ hu⟩
      invFun := fun u => ⟨key u,mem_image.mpr ⟨u,u.property,rfl⟩⟩
      left_inv := by
        intro z
        apply Subtype.ext
        obtain ⟨u,hu,huz⟩ := mem_image.mp z.property
        change key ((ofLex z.val).2) = z.val
        rw [← huz]
        rfl
      right_inv := by intro u; rfl }
  have hg : ∀ z : T, rho (g z) = (ofLex z.val).1 := by
    intro z
    obtain ⟨u,hu,huz⟩ := mem_image.mp z.property
    change rho (ofLex z.val).2 = (ofLex z.val).1
    rw [← huz]
    rfl
  have hT : T.card = ell*s := by rw [card_image_of_injective _ hkey,hcard]
  let f : Fin (ell*s) ≃o T := T.orderIsoOfFin hT
  let e : Fin ell × Fin s ≃ S := finProdFinEquiv.trans (f.toEquiv.trans g)
  refine ⟨e, ?_⟩
  intro a b x y hxy
  have hidx : finProdFinEquiv (a,x) ≤ finProdFinEquiv (b,y) := by
    change x.val+s*a.val ≤ y.val+s*b.val
    omega
  have he := f.monotone hidx
  change rho (g (f (finProdFinEquiv (a,x)))) ≤ rho (g (f (finProdFinEquiv (b,y))))
  rw [hg,hg]
  exact Prod.Lex.monotone_fst _ _ he

/-- The last vertex in a sorted block attains its maximum, and that
maximum is at most every weight in the next block. -/
theorem exists_sorted_blocks {V : Type*} [LinearOrder V]
    (S : Finset V) (rho : V → ℝ) {ell s : ℕ} (hs : 0 < s)
    (hcard : S.card = ell*s) {t : ℝ}
    (hrho : ∀ u ∈ S, t ≤ rho u ∧ rho u ≤ 1) :
    ∃ e : Fin ell × Fin s ≃ S, ∃ theta : Fin ell → ℝ,
      (∀ a, t ≤ theta a ∧ theta a ≤ 1) ∧
      (∀ a x, rho (e (a,x)) ≤ theta a) ∧
      (∀ a (ha : a.val+1 < ell) x,
        theta a ≤ rho (e (⟨a.val+1,ha⟩,x))) := by
  obtain ⟨e,he⟩ := exists_sorted_block_enumeration S rho hcard
  let last : Fin s := ⟨s-1, by omega⟩
  let theta := fun a => rho (e (a,last))
  refine ⟨e,theta,?_,?_,?_⟩
  · intro a
    exact hrho _ (e (a,last)).property
  · intro a x
    apply he
    change s*a.val+x.val ≤ s*a.val+(s-1)
    omega
  · intro a ha x
    apply he
    change s*a.val+(s-1) ≤ s*(a.val+1)+x.val
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- For selected eligible blocks, the sum of their logarithmic maxima
is controlled by the logarithms on all vertices. Omitted blocks cost
exactly their number times log tau. This is the sorted-block shift in A.1. -/
theorem sorted_block_log_bound {ell s : ℕ} (hs : 0 < s)
    (rho : Fin ell → Fin s → ℝ) (theta : Fin ell → ℝ)
    (M : Finset (Fin ell)) {t : ℝ} (ht : 0 < t)
    (hrho : ∀ a x, t ≤ rho a x)
    (htheta : ∀ a ∈ M, 0 < theta a)
    (heligible : ∀ a ∈ M, a.val+1 < ell)
    (hshift : ∀ a, ∀ ha : a ∈ M, ∀ x : Fin s,
      theta a ≤ rho ⟨a.val+1, heligible a ha⟩ x) :
    (s : ℝ)*(∑ a ∈ M, log (theta a)) ≤
      (∑ a, ∑ x, log (rho a x)) - (s : ℝ)*(ell-M.card)*log t := by
  let next : {a // a ∈ M} → Fin ell := fun a =>
    ⟨a.val.val+1, heligible a.val a.property⟩
  have hnext : Function.Injective next := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have hh := congrArg Fin.val hab
    change a.val.val+1 = b.val.val+1 at hh
    omega
  let T := M.attach.image next
  have hT : T.card = M.card := by rw [card_image_of_injective _ hnext, card_attach]
  have hsum : ∑ a ∈ M, ∑ x : Fin s, log (theta a) ≤
      ∑ b ∈ T, ∑ x : Fin s, log (rho b x) := by
    rw [show T = M.attach.image next from rfl, sum_image (fun a _ b _ h => hnext h)]
    rw [← sum_attach M (fun a => ∑ x : Fin s, log (theta a))]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro x hx
    exact log_le_log (htheta a.val a.property) (hshift a.val a.property x)
  have hrest : (s : ℝ)*(ell-M.card)*log t ≤
      ∑ b ∈ univ \ T, ∑ x : Fin s, log (rho b x) := by
    have hb : ∀ b, (s : ℝ)*log t ≤ ∑ x : Fin s, log (rho b x) := by
      intro b
      simpa using sum_le_sum (s := (univ : Finset (Fin s)))
        (fun x _ => log_le_log ht (hrho b x))
    have hh := sum_le_sum (s := univ \ T) (fun b _ => hb b)
    have hcard : (univ \ T).card = ell-M.card := by simp [card_sdiff, hT]
    simp only [sum_const, nsmul_eq_mul] at hh
    rw [hcard] at hh
    have hc : M.card ≤ ell := by rw [← hT]; simpa using (card_le_univ T)
    rw [Nat.cast_sub hc] at hh
    nlinarith
  have hall := sum_sdiff (subset_univ T) (f := fun b => ∑ x : Fin s, log (rho b x))
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [← mul_sum] at hsum
  linarith

/-- Product form of the sorted-block estimate. The input on the class
geometric mean is stated logarithmically, avoiding explicit roots. -/
theorem sorted_block_max_product {ell s : ℕ} (hs : 0 < s)
    (rho : Fin ell → Fin s → ℝ) (theta : Fin ell → ℝ)
    (M : Finset (Fin ell)) {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    (hrho : ∀ a x, t ≤ rho a x)
    (htheta : ∀ a ∈ M, 0 < theta a)
    (heligible : ∀ a ∈ M, a.val+1 < ell)
    (hshift : ∀ a, ∀ ha : a ∈ M, ∀ x : Fin s,
      theta a ≤ rho ⟨a.val+1, heligible a ha⟩ x)
    (hmean : (∑ a, ∑ x, log (rho a x)) ≤ (s : ℝ)*ell*log q) :
    (∏ a ∈ M, theta a) ≤ q^ell * t^(-((ell : ℝ)-M.card)) := by
  have hh := sorted_block_log_bound hs rho theta M ht hrho htheta heligible hshift
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : (∑ a ∈ M, log (theta a)) ≤
      (ell : ℝ)*log q - ((ell : ℝ)-M.card)*log t := by nlinarith
  apply (log_le_log_iff (prod_pos htheta)
    (mul_pos (pow_pos hq _) (rpow_pos_of_pos ht _))).mp
  rw [log_prod (fun a ha => (htheta a ha).ne'),
    log_mul (pow_pos hq _).ne' (rpow_pos_of_pos ht _).ne',
    log_pow, log_rpow ht]
  linarith

end HadwigerRamsey.ThomasonUpper
