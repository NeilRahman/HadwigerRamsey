import HadwigerRamsey.Existence.Sampling

open scoped Classical
namespace HadwigerRamsey
/-- Every edge of the complete graph has exactly one of three colours. -/
def IsThreeDecomposition {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n)) : Prop :=
  ∀ u v, u ≠ v → ∃! i, (G i).Adj u v

namespace Existence
def label : Fin 3 → Label := ![none,some false,some true]
lemma label_unique (a : Label) : ∃! i : Fin 3, label i = a := by
  cases a with
  | none => refine ⟨0,rfl,?_⟩; intro i hi; fin_cases i <;> simp_all [label]
  | some b => cases b
              · refine ⟨1,rfl,?_⟩; intro i hi; fin_cases i <;> simp_all [label]
              · refine ⟨2,rfl,?_⟩; intro i hi; fin_cases i <;> simp_all [label]
lemma colourGraph_decomposition {n : ℕ} (ω : Edge n → Label) :
    IsThreeDecomposition (fun i => colourGraph (label i) ω) := by
  intro u v huv
  obtain ⟨i,hi,hunique⟩ := label_unique (ω (edgeOf u v huv))
  refine ⟨i,⟨huv,hi.symm⟩,?_⟩
  intro j ⟨h,hj⟩
  exact hunique j hj.symm
end Existence

lemma IsThreeDecomposition.comap {n m : ℕ} {G : Fin 3 → SimpleGraph (Fin n)}
    (hG : IsThreeDecomposition G) (f : Fin m → Fin n) (hf : Function.Injective f) :
    IsThreeDecomposition (fun i => (G i).comap f) := by
  intro u v huv
  exact hG (f u) (f v) (hf.ne huv)
end HadwigerRamsey
