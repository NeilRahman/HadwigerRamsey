import HadwigerRamsey.Main.Partition
import HadwigerRamsey.Main.Conservation
import HadwigerRamsey.Main.DensityLoss
import HadwigerRamsey.Main.Restriction

open scoped Classical BigOperators
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.Main

lemma PartitionData.mass_nonneg {n : ℕ} {G : SimpleGraph (Fin n)}
    {lam η δ : ℝ} (D : PartitionData G lam η δ) (i : Fin (D.m+1)) :
    0 ≤ classMass D.classes i := classMass_nonneg D.classes i

lemma PartitionData.mass_sum {n : ℕ} {G : SimpleGraph (Fin n)}
    {lam η δ : ℝ} (D : PartitionData G lam η δ) (hn : 0 < n) :
    ∑ i, classMass D.classes i = 1 := sum_classMass hn D.classes

lemma PartitionData.mass_dummy {n : ℕ} {G : SimpleGraph (Fin n)}
    {lam η δ : ℝ} (D : PartitionData G lam η δ) (hn : 0 < n) :
    classMass D.classes (Fin.last D.m) ≤ 21*lam := by
  change ((classVertices D.classes (Fin.last D.m)).card : ℝ)/(n : ℝ) ≤ _
  rw [D.classVertices_classes]
  apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  simpa only [mul_assoc] using D.dummy_size

/-- Restrict the two colours to their near-spanning sets; conservation yields the
approximate diagonal and off-diagonal constraints needed for optimization. -/
theorem density_feasibility {n : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {lam η δ e ξ : ℝ} (D : PartitionData (G k) lam η δ)
    (P Q : Finset (Fin n)) (hlam : 0 < lam) (he : 0 ≤ e) (hξ : 0 ≤ ξ)
    (heξ : e ≤ lam*ξ/100) (hηξ : η/lam ≤ ξ/4)
    (hP : (1-e)*n ≤ (P.card : ℝ)) (hQ : (1-e)*n ≤ (Q.card : ℝ))
    (hcard : ∀ u : Fin D.m, 2 ≤ (D.V u.castSucc).card) :
    (∀ u : Fin D.m, 1-ξ ≤ internalDensity (G k) (D.V u.castSucc)+
      restrictedDensity (G i) D.V P u u+restrictedDensity (G j) D.V Q u u) ∧
    (∀ u v : Fin D.m, u ≠ v → 1-ξ ≤
      restrictedDensity (G i) D.V P u v+restrictedDensity (G j) D.V Q u v) := by
  have hediv : e/lam ≤ ξ/100 := (div_le_iff₀ hlam).mpr (by nlinarith only [heξ])
  constructor
  · intro u
    have hLP := internalDensity_inter_loss (G i) (D.V u.castSucc) P hlam he
      (hcard u) (D.active_size u) hP
    have hLQ := internalDensity_inter_loss (G j) (D.V u.castSucc) Q hlam he
      (hcard u) (D.active_size u) hQ
    have hh := restricted_diagonal_conservation G hG (D.V u.castSucc) P Q
      (hcard u) i j k hij hik hjk hLP hLQ
      (show 2*(8*e/lam) ≤ ξ by
        calc
          _ = 16*(e/lam) := by ring
          _ ≤ ξ := by linarith only [hediv,hξ])
    simpa [restrictedDensity] using hh
  · intro u v huv
    have hLP := edgeDensity_inter_loss (G i) (D.V u.castSucc) (D.V v.castSucc) P
      hlam he (D.active_size u) (D.active_size v) hP
    have hLQ := edgeDensity_inter_loss (G j) (D.V u.castSucc) (D.V v.castSucc) Q
      hlam he (D.active_size u) (D.active_size v) hQ
    have hdis := D.pairwise (show u.castSucc ≠ v.castSucc by
      intro hh; exact huv (Fin.castSucc_injective _ hh))
    have hnU : (D.V u.castSucc).Nonempty := card_pos.mp (by have := hcard u; omega)
    have hnV : (D.V v.castSucc).Nonempty := card_pos.mp (by have := hcard v; omega)
    have hh := restricted_offdiagonal_conservation G hG (D.V u.castSucc) (D.V v.castSucc)
      P Q hdis hnU hnV i j k hij hik hjk hLP hLQ (D.cross u v huv)
      (show η/lam+2*(2*e/lam) ≤ ξ by
        calc
          _ = η/lam+4*(e/lam) := by ring
          _ ≤ ξ := by linarith only [hediv,hηξ,hξ])
    simpa [restrictedDensity,huv] using hh

end HadwigerRamsey.Main
