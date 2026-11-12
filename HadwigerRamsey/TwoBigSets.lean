import HadwigerRamsey.ConnectedSets
import HadwigerRamsey.TwoBigSets.Finite
import HadwigerRamsey.TwoBigSets.Partitions
import HadwigerRamsey.TwoBigSets.Minor
import HadwigerRamsey.TwoBigSets.Parameters

open scoped Classical
open Finset Real

namespace HadwigerRamsey
namespace TwoBigSets
open ControlledPartition

/-- One colour has the sparse or almost-spanning connected outcome of Lemma 3.6. -/
def Good {n : ℕ} (G : SimpleGraph (Fin n)) (ε δ : ℝ) : Prop :=
  (G.edgeFinset.card : ℝ) ≤ 3*ε*(n : ℝ)^2 ∨
    ∃ S : Finset (Fin n), (1-ε)*n ≤ (S.card : ℝ) ∧ RealConnected G S (δ*n)

theorem small_parts_of_not_good {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) {ε r η δ : ℝ} (hr : 0 ≤ r) (hre : r ≤ 2*ε/3)
    (P : Decomposition n) (hP : Controlled G r η δ P) (hbad : ¬Good G ε δ) :
    ∀ S ∈ insert P.Y P.parts, (S.card : ℝ) ≤ (1-ε)*n := by
  have hdense : 3*ε*(n : ℝ)^2 < G.edgeFinset.card :=
    lt_of_not_ge (fun h => hbad (Or.inl h))
  intro S hS
  rcases mem_insert.mp hS with rfl | hS
  · exact (remainder_small G hn hr hre hP.2.2.1 hdense).le
  · exact (lt_of_not_ge (fun h => hbad (Or.inr ⟨S,h,hP.2.1 S hS⟩))).le

end TwoBigSets
open TwoBigSets ControlledPartition

/-- Lemma 3.6, explicitly using the controlled-partition theorem `connectedsets`. -/
theorem twobigsets (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ n ≥ n₀, ∀ G : Fin 3 → SimpleGraph (Fin n), IsThreeDecomposition G →
        (∃ i j : Fin 3, i ≠ j ∧ Good (G i) ε δ ∧ Good (G j) ε δ) ∨
        (∃ i : Fin 3, C*n/sqrt (log (n : ℝ)) ≤ (hadwigerNumber (G i) : ℝ)) := by
  classical
  obtain ⟨r,hr,hrs,hre,hgap⟩ := small_parameter ε hε
  let K := 2*C/r^3
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨γ,hγ,N,hN,hbip⟩ := bipMinor K hK
  let η := r^3*γ/4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hpartition⟩ := connectedsets r η hr hη
  let n₀ := ⌈2*(N+2 : ℕ)/r^3⌉₊+1
  refine ⟨n₀,by dsimp [n₀]; omega,δ,hδ,?_⟩
  intro n hn G hG
  have hnpos : 0 < n := by dsimp [n₀] at hn; omega
  rcases two_good_or_two_bad (fun i => Good (G i) ε δ) with hgood | hbad
  · exact Or.inl hgood
  obtain ⟨i,j,k,hij,hik,hjk,hi,hj⟩ := hbad
  obtain ⟨P,hP⟩ := hpartition n (G i)
  obtain ⟨Q,hQ⟩ := hpartition n (G j)
  obtain ⟨A,B,hdis,hAB,hsize,hAp,hAq⟩ := large_separated_sets (G i) (G j) P Q
    hnpos hr hrs hgap hP hQ
    (small_parts_of_not_good (G i) hnpos hr.le hre P hP hi)
    (small_parts_of_not_good (G j) hnpos hr.le hre Q hQ hj)
  obtain ⟨S,hS,T,hT,hAS,hBT,hST⟩ := hAp
  obtain ⟨U,hU,V,hV,hAU,hBV,hUV⟩ := hAq
  have hmemP : ∀ W ∈ insert P.Y P.parts, W ∈ P.parts ∨ W = P.Y := by
    intro W hW
    exact (mem_insert.mp hW).symm
  have hmemQ : ∀ W ∈ insert Q.Y Q.parts, W ∈ Q.parts ∨ W = Q.Y := by
    intro W hW
    exact (mem_insert.mp hW).symm
  have hcrossi := cross_le_controlled (G i) P hP hη.le S T A B
    (hmemP S hS) (hmemP T hT) hST hAS hBT hAB
  have hcrossj := cross_le_controlled (G j) Q hQ hη.le U V A B
    (hmemQ U hU) (hmemQ V hV) hUV hAU hBV hAB
  have hcross := third_cross_lower G hG i j k hij hik hjk A B hdis hAB η hcrossi hcrossj
  have hdensity : (1-γ)*(A.card : ℝ)^2 ≤ ((G k).interedges A B).card := by
    have hh := mul_le_mul_of_nonneg_right hsize
      (mul_nonneg hγ.le (Nat.cast_nonneg A.card))
    dsimp only [η] at hcross
    nlinarith only [hh,hcross]
  have hlarge : (N+2 : ℕ) ≤ A.card := by
    have hceil : ⌈2*(N+2 : ℕ)/r^3⌉₊ ≤ n := by dsimp [n₀] at hn; omega
    have hh : 2*(N+2 : ℕ)/r^3 ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have hh' := (div_le_iff₀ (show 0 < r^3 by positivity)).mp hh
    have hh'' : ((N+2 : ℕ) : ℝ) ≤ A.card := by nlinarith only [hh',hsize]
    exact_mod_cast hh''
  have hminor := cross_minor (G k) A B hdis hAB (show N ≤ A.card by omega) hbip hdensity
  have hfinal := final_comparison hr hC (show 2 ≤ A.card by omega)
    (show A.card ≤ n by simpa using A.card_le_univ) hsize
  exact Or.inr ⟨k,hfinal.trans hminor⟩

end HadwigerRamsey
