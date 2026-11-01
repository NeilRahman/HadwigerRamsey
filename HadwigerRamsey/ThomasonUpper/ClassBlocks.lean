import HadwigerRamsey.ThomasonUpper.SortedNonneighbors
import HadwigerRamsey.ThomasonUpper.BlockPartitions

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Assemble the classwise block enumerations into a single enumeration
of all vertices, retaining the original class labels. -/
noncomputable def classBlockEnumeration {n k s : ℕ} (classes : Fin n → Fin k)
    (ell : Fin k → ℕ) (e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i) :
    (Σ i, Fin (ell i)) × Fin s ≃ Fin n := by
  let f : ∀ i, classVertices classes i ≃ {v // classes v = i} := fun i =>
    { toFun := fun u => ⟨u.val,(mem_filter.mp u.property).2⟩
      invFun := fun u => ⟨u.val,mem_filter.mpr ⟨mem_univ _,u.property⟩⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  exact (Equiv.sigmaProdDistrib (fun i => Fin (ell i)) (Fin s)).trans
    ((Equiv.sigmaCongrRight (fun i => (e i).trans (f i))).trans
      (Equiv.sigmaFiberEquiv classes))

theorem classBlockEnumeration_apply {n k s : ℕ} (classes : Fin n → Fin k)
    (ell : Fin k → ℕ) (e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i)
    (i : Fin k) (a : Fin (ell i)) (x : Fin s) :
    classBlockEnumeration classes ell e (⟨i,a⟩,x) = e i (a,x) := rfl

theorem classBlockEnumeration_class {n k s : ℕ} (classes : Fin n → Fin k)
    (ell : Fin k → ℕ) (e : ∀ i, Fin (ell i) × Fin s ≃ classVertices classes i)
    (i : Fin k) (a : Fin (ell i)) (x : Fin s) :
    classes (classBlockEnumeration classes ell e (⟨i,a⟩,x)) = i :=
  (mem_filter.mp (e i (a,x)).property).2

/-- Counting a property block by block counts precisely the vertices in
the class with that property. -/
theorem sum_block_filter_card {V : Type*} [DecidableEq V] (S : Finset V)
    {ell s : ℕ} (e : Fin ell × Fin s ≃ S) (P : V → Prop) [DecidablePred P] :
    (∑ a, (univ.filter (fun x : Fin s => P (e (a,x)))).card) = (S.filter P).card := by
  classical
  have hc : ∀ a, (univ.filter (fun x : Fin s => P (e (a,x)))).card =
      ∑ x : Fin s, if P (e (a,x)) then (1 : ℕ) else 0 := by
    intro a
    simp
  simp_rw [hc]
  calc
    _ = ∑ z : Fin ell × Fin s, if P (e z) then (1 : ℕ) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = ∑ u : S, if P u then (1 : ℕ) else 0 :=
      e.sum_comp (fun u : S => if P u then (1 : ℕ) else 0)
    _ = ∑ u ∈ S, if P u then (1 : ℕ) else 0 :=
      sum_coe_sort S (fun u => if P u then (1 : ℕ) else 0)
    _ = _ := by simp

end HadwigerRamsey.ThomasonUpper
