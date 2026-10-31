import HadwigerRamsey.ThomasonUpper.Density
import HadwigerRamsey.ThomasonUpper.Stability
import HadwigerRamsey.ThomasonUpper.InducedDensity

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- Express the manuscript's diagonal density as an ordinary relation
density on the possible ordered pairs of distinct vertices. -/
theorem internalDensity_eq_offDiag_density {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    internalDensity G S =
      (Rel.edgeDensity (fun (e : V × V) (_ : Unit) => G.Adj e.1 e.2)
        S.offDiag {()} : ℝ) := by
  classical
  have hnum : (Rel.interedges (fun (e : V × V) (_ : Unit) => G.Adj e.1 e.2)
      S.offDiag {()}).card = (G.interedges S S).card := by
    apply card_bij (fun e _ => e.1)
    · intro e he
      obtain ⟨heS, _, heG⟩ := Rel.mem_interedges_iff.mp he
      exact G.mem_interedges_iff.mpr ⟨(mem_offDiag.mp heS).1,
        (mem_offDiag.mp heS).2.1, heG⟩
    · intro e _ f _ hef
      exact Prod.ext hef (Subsingleton.elim _ _)
    · intro e he
      obtain ⟨hx, hy, hxy⟩ := G.mem_interedges_iff.mp he
      exact ⟨(e, ()), Rel.mem_interedges_iff.mpr
        ⟨mem_offDiag.mpr ⟨hx, hy, G.ne_of_adj hxy⟩, by simp, hxy⟩, rfl⟩
  have hden : S.offDiag.card = 2 * S.card.choose 2 := by
    rw [offDiag_card, Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self S.card).two_dvd]
    exact (Nat.mul_sub_one S.card S.card).symm
  rw [Rel.edgeDensity, hnum, card_internal_interedges, hden]
  simp only [card_singleton, Nat.cast_mul, Nat.cast_ofNat, Rat.cast_div,
    Rat.cast_mul, Rat.cast_natCast, Nat.cast_one, mul_one, internalDensity]
  ring

/-- Deleting z vertices from a class loses at most a 4z/s fraction of
its possible ordered pairs. No lower bound on the surviving size is needed. -/
theorem offDiag_survives_deletion {V : Type*} [DecidableEq V]
    (S Z : Finset V) (hS : 2 ≤ S.card) :
    (1 - 4 * (Z.card : ℝ) / S.card) * (S.offDiag.card : ℝ) ≤
      ((S \ Z).offDiag.card : ℝ) := by
  have hs : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
  have ht : ((S \ Z).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card sdiff_subset
  have hdel : (S.card : ℝ) ≤ (S \ Z).card + Z.card := by
    exact_mod_cast card_le_card_sdiff_add_card (s := S) (t := Z)
  have hoff (A : Finset V) : (A.offDiag.card : ℝ) = (A.card : ℝ)^2 - A.card := by
    rw [offDiag_card, Nat.cast_sub (by nlinarith : A.card ≤ A.card * A.card)]
    push_cast
    ring
  rw [hoff, hoff]
  have hs0 : (S.card : ℝ) ≠ 0 := by linarith
  have hid : (1 - 4 * (Z.card : ℝ) / S.card) * ((S.card : ℝ)^2 - S.card) =
      (S.card : ℝ)^2 - S.card - 4 * Z.card * (S.card - 1) := by field_simp
  rw [hid]
  have hz : (0 : ℝ) ≤ Z.card := by positivity
  have ht0 : (0 : ℝ) ≤ (S \ Z).card := by positivity
  have hdiff : (S.card : ℝ) - (S \ Z).card ≤ Z.card := by linarith
  have hprod := mul_le_mul_of_nonneg_right hdiff (by linarith : (0 : ℝ) ≤ 2*S.card)
  nlinarith [sq_nonneg ((S.card : ℝ) - (S \ Z).card),
    mul_nonneg hz (by linarith : (0 : ℝ) ≤ 2 * S.card - 4)]

/-- The diagonal part of A.2 reuses Mathlib's relation-density deletion
estimate after changing the sample space to distinct vertex pairs. -/
theorem internalDensity_deletion_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S Z : Finset V) (hS : 2 ≤ S.card) :
    |internalDensity G (S \ Z) - internalDensity G S| ≤ 8 * (Z.card : ℝ) / S.card := by
  classical
  rw [internalDensity_eq_offDiag_density, internalDensity_eq_offDiag_density]
  have h := Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul
    (𝕜 := ℝ) (fun (e : V × V) (_ : Unit) => G.Adj e.1 e.2)
    (offDiag_mono sdiff_subset) (Subset.refl ({()} : Finset Unit))
    (by positivity : 0 ≤ 4 * (Z.card : ℝ) / S.card)
    (offDiag_survives_deletion S Z hS)
    (by simp; positivity : (1 - 4 * (Z.card : ℝ) / S.card) *
      (({()} : Finset Unit).card : ℝ) ≤ ({()} : Finset Unit).card)
  have he : (2 : ℝ) * (4 * Z.card / S.card) = 8 * Z.card / S.card := by ring
  rw [he] at h
  exact h

/-- A class loses at most the global deletion fraction divided by its
original mass. This supplies Mathlib's retained-cardinality hypothesis. -/
theorem retained_card_fraction {V : Type*} [DecidableEq V]
    (S Z : Finset V) {a δ N : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (hS : a * N ≤ S.card) (hZ : (Z.card : ℝ) ≤ δ * N) :
    (1 - δ / a) * (S.card : ℝ) ≤ (S \ Z).card := by
  have hdel : (S.card : ℝ) ≤ (S \ Z).card + Z.card := by
    exact_mod_cast card_le_card_sdiff_add_card (s := S) (t := Z)
  have hm := mul_le_mul_of_nonneg_left hS (div_nonneg hδ ha.le)
  have hid : δ / a * (a * N) = δ * N := by field_simp
  rw [hid] at hm
  nlinarith

/-- The off-diagonal part of A.2 is directly Mathlib's density estimate. -/
theorem edgeDensity_deletion_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T Z : Finset V) {a δ N : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ)
    (hS : a * N ≤ S.card) (hT : a * N ≤ T.card)
    (hZ : (Z.card : ℝ) ≤ δ * N) :
    |(G.edgeDensity (S \ Z) (T \ Z) : ℝ) - G.edgeDensity S T| ≤ 2 * δ / a := by
  have h := Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul (𝕜 := ℝ) G.Adj
    (sdiff_subset : S \ Z ⊆ S) (sdiff_subset : T \ Z ⊆ T)
    (div_nonneg hδ ha.le)
    (retained_card_fraction S Z ha hδ hS hZ)
    (retained_card_fraction T Z ha hδ hT hZ)
  simpa only [SimpleGraph.edgeDensity, mul_div_assoc] using h

/-- The elementary normalization estimate for the class masses in A.2. -/
theorem normalized_mass_deletion_bound {N z s t δ : ℝ}
    (hN : 0 < N) (hz : 0 ≤ z) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (hzδ : z ≤ δ * N) (ht : 0 ≤ t) (hts : t ≤ s)
    (hsN : s ≤ N) (hloss : s ≤ t + z) :
    |t / (N-z) - s/N| ≤ 2*δ := by
  have hzhalf : z ≤ N/2 := by nlinarith
  have hNp : 0 < N-z := by linarith
  have hs : 0 ≤ s := ht.trans hts
  have hnum : |N*t - s*(N-z)| ≤ N*z := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hs hz, mul_le_mul_of_nonneg_left hloss hN.le]
    · nlinarith [mul_le_mul_of_nonneg_left hts hN.le,
        mul_le_mul_of_nonneg_right hsN hz]
  have he : t/(N-z)-s/N = (N*t-s*(N-z))/(N*(N-z)) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hN hNp)]
  apply (div_le_iff₀ (mul_pos hN hNp)).mpr
  have hzbound : z ≤ 2*δ*(N-z) := by
    nlinarith [mul_nonneg hδ (by linarith : 0 ≤ N-2*z)]
  nlinarith [mul_le_mul_of_nonneg_left hzbound hN.le]

/-- The class masses and block densities after deleting vertices are
computed in the original graph, whose induced graph has identical adjacency
on all surviving vertices. -/
noncomputable def deletedClassMass {n k : ℕ} (τ : Fin n → Fin k)
    (Z : Finset (Fin n)) (i : Fin k) : ℝ :=
  ((classVertices τ i \ Z).card : ℝ) / (n - Z.card : ℕ)

noncomputable def deletedBlockDensity {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (Z : Finset (Fin n)) (i j : Fin k) : ℝ :=
  if i = j then internalDensity G (classVertices τ i \ Z)
  else (G.edgeDensity (classVertices τ i \ Z) (classVertices τ j \ Z) : ℝ)

/-- The actual class fiber in the induced graph obtained by deletion. -/
def survivingClassVertices {n k : ℕ} (τ : Fin n → Fin k) (Z : Finset (Fin n))
    (i : Fin k) : Finset {v : Fin n // v ∉ Z} :=
  univ.filter fun v => τ v.val = i

theorem image_survivingClassVertices {n k : ℕ} (τ : Fin n → Fin k)
    (Z : Finset (Fin n)) (i : Fin k) :
    (survivingClassVertices τ Z i).image Subtype.val = classVertices τ i \ Z := by
  classical
  ext v
  simp only [survivingClassVertices, mem_image, mem_filter, mem_univ, true_and,
    mem_sdiff, classVertices]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa using hx, x.property⟩
  · rintro ⟨hx, hv⟩
    exact ⟨⟨v,hv⟩, by simpa using hx, rfl⟩

theorem deletedClassMass_eq_induced {n k : ℕ} (τ : Fin n → Fin k)
    (Z : Finset (Fin n)) (i : Fin k) :
    deletedClassMass τ Z i = ((survivingClassVertices τ Z i).card : ℝ) /
      Fintype.card {v : Fin n // v ∉ Z} := by
  classical
  have hnum : (survivingClassVertices τ Z i).card = (classVertices τ i \ Z).card := by
    rw [← image_survivingClassVertices τ Z i]
    exact (card_image_of_injective _ Subtype.val_injective).symm
  have hden : Fintype.card {v : Fin n // v ∉ Z} = n-Z.card := by
    rw [Fintype.card_of_subtype (univ \ Z) (by intro v; simp),
      card_sdiff_of_subset (subset_univ Z), card_univ, Fintype.card_fin]
  simp only [deletedClassMass, hnum, hden]

/-- The deletion density is exactly the block density in G-Z, with its
surviving fibers, including the diagonal unordered-pair convention. -/
theorem deletedBlockDensity_eq_induced {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (Z : Finset (Fin n)) (i j : Fin k) :
    deletedBlockDensity G τ Z i j =
      if i = j then internalDensity (G.induce ((Z : Set (Fin n))ᶜ)) (survivingClassVertices τ Z i)
      else ((G.induce ((Z : Set (Fin n))ᶜ)).edgeDensity
        (survivingClassVertices τ Z i) (survivingClassVertices τ Z j) : ℝ) := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [deletedBlockDensity, if_pos rfl]
    have hh := internalDensity_induced G ((Z : Set (Fin n))ᶜ) (survivingClassVertices τ Z i)
    exact (hh.trans (congrArg (internalDensity G) (image_survivingClassVertices τ Z i))).symm
  · simp only [deletedBlockDensity, if_neg hij]
    have hh := edgeDensity_induced G ((Z : Set (Fin n))ᶜ)
      (survivingClassVertices τ Z i) (survivingClassVertices τ Z j)
    have he := hh.trans (congrArg₂ G.edgeDensity
      (image_survivingClassVertices τ Z i) (image_survivingClassVertices τ Z j))
    exact congrArg (fun q : ℚ => (q : ℝ)) he.symm

theorem deletedBlockDensity_bounds {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (Z : Finset (Fin n)) (i j : Fin k) :
    0 ≤ deletedBlockDensity G τ Z i j ∧ deletedBlockDensity G τ Z i j ≤ 1 := by
  classical
  unfold deletedBlockDensity
  split
  · exact ⟨internalDensity_nonneg _ _, internalDensity_le_one _ _⟩
  · exact ⟨by exact_mod_cast G.edgeDensity_nonneg _ _,
      by exact_mod_cast G.edgeDensity_le_one _ _⟩

noncomputable def deletedLambda {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (Z : Finset (Fin n)) : ℝ :=
  ∑ i, ∑ j, deletedClassMass τ Z i * deletedClassMass τ Z j *
    (-log (1 - deletedBlockDensity G τ Z i j))

theorem deletedClassMass_nonneg {n k : ℕ} (τ : Fin n → Fin k)
    (Z : Finset (Fin n)) (i : Fin k) : 0 ≤ deletedClassMass τ Z i := by
  unfold deletedClassMass
  positivity

theorem sum_deletedClassMass {n k : ℕ} (τ : Fin n → Fin k)
    (Z : Finset (Fin n)) (hZ : Z.card < n) :
    ∑ i, deletedClassMass τ Z i = 1 := by
  classical
  have h := card_eq_sum_card_fiberwise (s := univ \ Z) (t := univ) (f := τ)
    (by intro v _; exact mem_univ _)
  have hf : ∀ i, ((univ \ Z).filter fun v => τ v = i) = classVertices τ i \ Z := by
    intro i
    ext v
    simp [classVertices, and_comm]
  simp_rw [hf] at h
  rw [card_sdiff_of_subset (subset_univ Z), card_univ, Fintype.card_fin] at h
  simp only [deletedClassMass, ← sum_div, ← Nat.cast_sum, ← h]
  exact div_self (by exact_mod_cast (by omega : n - Z.card ≠ 0))

/-- The combinatorial part of appendix A.2, with an explicit size threshold
and constants: all class masses change by at most 2δ, and all block
densities (including diagonal blocks) by at most 8δ/a. -/
theorem vertex_deletion_bounds {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (Z : Finset (Fin n)) {a δ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 ≤ δ) (hδa : δ < a/2)
    (hn : 4 ≤ a*n) (hZ : (Z.card : ℝ) ≤ δ*n)
    (hsize : ∀ i, a*n ≤ (classVertices τ i).card) :
    Z.card < n ∧
      (∀ i, a*n/2 ≤ ((classVertices τ i \ Z).card : ℝ)) ∧
      (∀ i, |deletedClassMass τ Z i - classMass τ i| ≤ 2*δ) ∧
      (∀ i j, |deletedBlockDensity G τ Z i j - blockDensity G τ i j| ≤ 8*δ/a) := by
  classical
  have hnR : (0 : ℝ) < n := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hδhalf : δ ≤ 1/2 := by linarith
  have hZltR : (Z.card : ℝ) < n := by nlinarith
  have hZlt : Z.card < n := by exact_mod_cast hZltR
  have hsub : ((n - Z.card : ℕ) : ℝ) = (n : ℝ) - Z.card :=
    Nat.cast_sub hZlt.le
  have hremain : ∀ i, a*n/2 ≤ ((classVertices τ i \ Z).card : ℝ) := by
    intro i
    have hc : ((classVertices τ i).card : ℝ) ≤
        (classVertices τ i \ Z).card + Z.card := by
      exact_mod_cast card_le_card_sdiff_add_card (s := classVertices τ i) (t := Z)
    have hδn := mul_lt_mul_of_pos_right hδa hnR
    nlinarith [hsize i]
  refine ⟨hZlt, hremain, ?_, ?_⟩
  · intro i
    unfold deletedClassMass classMass
    rw [hsub]
    apply normalized_mass_deletion_bound hnR (by positivity) hδ hδhalf hZ (by positivity)
    · exact_mod_cast (card_le_card sdiff_subset : (classVertices τ i \ Z).card ≤ _)
    · change ((classVertices τ i).card : ℝ) ≤ n
      have hc : (classVertices τ i).card ≤ n := by
        simpa only [card_univ, Fintype.card_fin] using card_le_univ (classVertices τ i)
      exact_mod_cast hc
    · exact_mod_cast card_le_card_sdiff_add_card (s := classVertices τ i) (t := Z)
  · intro i j
    have hi : 2 ≤ (classVertices τ i).card := by
      have := hsize i
      exact_mod_cast (by linarith : (2 : ℝ) ≤ (classVertices τ i).card)
    have hspos : (0 : ℝ) < (classVertices τ i).card := by exact_mod_cast (by omega : 0 < (classVertices τ i).card)
    have hratio : (Z.card : ℝ) / (classVertices τ i).card ≤ δ/a := by
      apply (div_le_div_iff₀ hspos ha).mpr
      nlinarith [mul_le_mul_of_nonneg_left (hsize i) hδ,
        mul_le_mul_of_nonneg_right hZ ha.le]
    by_cases hij : i = j
    · subst j
      simp only [deletedBlockDensity, blockDensity]
      calc
        _ ≤ 8 * (Z.card : ℝ) / (classVertices τ i).card := internalDensity_deletion_bound G _ Z hi
        _ ≤ 8*δ/a := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hratio (by norm_num : (0:ℝ) ≤ 8)
    · simp only [deletedBlockDensity, blockDensity, if_neg hij]
      exact (edgeDensity_deletion_bound G _ _ Z ha hδ (hsize i) (hsize j) hZ).trans
        (by apply div_le_div_of_nonneg_right _ ha.le; linarith)

/-- The entropy conclusion of appendix A.2, with a uniform explicit
constant. This combines actual graph-deletion estimates with the previously
checked analytic stability lemma. -/
theorem vertex_deletion_lambda_bound {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (Z : Finset (Fin n)) {a δ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 ≤ δ) (hδa : δ < a/2)
    (hn : 4 ≤ a*n) (hZ : (Z.card : ℝ) ≤ δ*n)
    (hsize : ∀ i, a*n ≤ (classVertices τ i).card)
    (hq : ∀ i j, a ≤ 1 - blockDensity G τ i j)
    (hsmall : 8*δ/a ≤ a/2) :
    (∀ i j, a/2 ≤ 1 - deletedBlockDensity G τ Z i j) ∧
      |deletedLambda G τ Z - blockLambda τ (blockDensity G τ)| ≤
        (16/a^2 + 4*log (2/a)/a)*δ := by
  classical
  have hb := vertex_deletion_bounds G τ Z ha ha1 hδ hδa hn hZ hsize
  have hnR : (0 : ℝ) < n := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnN : 0 < n := by exact_mod_cast hnR
  have haα : ∀ i, a ≤ classMass τ i := by
    intro i
    exact (le_div_iff₀ hnR).mpr (hsize i)
  have hsumα := sum_classMass hnN τ
  have hk : (k : ℝ)*a ≤ 1 := by
    calc
      _ = ∑ _i : Fin k, a := by simp
      _ ≤ ∑ i, classMass τ i := sum_le_sum fun i _ => haα i
      _ = 1 := hsumα
  have hsumdiff : (∑ i, |classMass τ i - deletedClassMass τ Z i|) ≤ 2*δ/a := by
    calc
      _ ≤ ∑ _i : Fin k, 2*δ := sum_le_sum fun i _ => by
        simpa only [abs_sub_comm] using hb.2.2.1 i
      _ = (k : ℝ)*(2*δ) := by simp
      _ ≤ 2*δ/a := (le_div_iff₀ ha).mpr (by nlinarith [mul_le_mul_of_nonneg_right hk hδ])
  have hr : ∀ i j, a/2 ≤ 1 - deletedBlockDensity G τ Z i j := by
    intro i j
    have hh := (abs_le.mp (hb.2.2.2 i j)).2
    linarith [hq i j]
  refine ⟨hr, ?_⟩
  have hlog : 0 ≤ log (2/a) := log_nonneg (by apply (le_div_iff₀ ha).mpr; linarith)
  have hl := lambda_stability (classMass τ) (deletedClassMass τ Z)
    (fun i j => 1 - blockDensity G τ i j)
    (fun i j => 1 - deletedBlockDensity G τ Z i j)
    (a := a/2) (d := 8*δ/a) (by linarith) (by linarith)
    (classMass_nonneg τ) (deletedClassMass_nonneg τ Z)
    hsumα (sum_deletedClassMass τ Z hb.1)
    (fun i j => ⟨by linarith [hq i j], by linarith [blockDensity_nonneg G τ i j]⟩)
    (fun i j => ⟨hr i j, by linarith [(deletedBlockDensity_bounds G τ Z i j).1]⟩)
    (fun i j => by
      have he : (1 - blockDensity G τ i j) - (1 - deletedBlockDensity G τ Z i j) =
          deletedBlockDensity G τ Z i j - blockDensity G τ i j := by ring
      rw [he]
      exact hb.2.2.2 i j)
  have hid : (1 : ℝ)/(a/2) = 2/a := by field_simp
  rw [hid] at hl
  have he : (8*δ/a)/(a/2) = 16*δ/a^2 := by field_simp; ring
  rw [he] at hl
  have hm := mul_le_mul_of_nonneg_left hsumdiff (by positivity : 0 ≤ 2*log (2/a))
  have hfinal := hl.trans (add_le_add (le_refl (16*δ/a^2)) hm)
  change |blockLambda τ (blockDensity G τ) - deletedLambda G τ Z| ≤ _ at hfinal
  rw [abs_sub_comm] at hfinal
  convert hfinal using 1; ring

/-- Appendix A.2 with one constant depending only on a and a uniform
order threshold. Complementary densities are written as 1 minus density;
their pointwise changes equal the corresponding density changes. -/
theorem vertex_deletion_stability (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), ∀ k : ℕ, ∀ τ : Fin n → Fin k,
      ∀ Z : Finset (Fin n), ∀ δ : ℝ,
      0 ≤ δ → δ < a/2 → (Z.card : ℝ) ≤ δ*n →
      (∀ i, a*n ≤ (classVertices τ i).card) →
      (∀ i, |deletedClassMass τ Z i - classMass τ i| ≤ C*δ) ∧
      (∀ i j, |deletedBlockDensity G τ Z i j - blockDensity G τ i j| ≤ C*δ ∧
        |(1 - deletedBlockDensity G τ Z i j) - (1 - blockDensity G τ i j)| ≤ C*δ) ∧
      ((∀ i j, a ≤ 1 - blockDensity G τ i j) → C*δ ≤ a/2 →
        (∀ i j, a/2 ≤ 1 - deletedBlockDensity G τ Z i j) ∧
        |deletedLambda G τ Z - blockLambda τ (blockDensity G τ)| ≤ C*δ) := by
  classical
  let C := 2 + 8/a + 16/a^2 + 4*|log (2/a)|/a
  have hC2 : 2 ≤ C := by
    dsimp [C]
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 8) ha.le,
      div_nonneg (by norm_num : (0:ℝ) ≤ 16) (sq_nonneg a),
      div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (abs_nonneg (log (2/a)))) ha.le]
  have hC8 : 8/a ≤ C := by
    dsimp [C]
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 16) (sq_nonneg a),
      div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (abs_nonneg (log (2/a)))) ha.le]
  have hCL : 16/a^2 + 4*log (2/a)/a ≤ C := by
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self (log (2/a))) (by norm_num : (0:ℝ) ≤ 4)) ha.le
    dsimp [C]
    nlinarith [div_nonneg (by norm_num : (0:ℝ) ≤ 8) ha.le]
  refine ⟨C, by linarith, ⌈4/a⌉₊ + 1, ?_⟩
  intro n hn G k τ Z δ hδ hδa hZ hsize
  have hnN : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnN
  have hn4 : 4 ≤ a*n := by
    have hh := Nat.le_ceil (4/a)
    have hnceil : (⌈4/a⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈4/a⌉₊ ≤ n)
    have hdiv : 4/a ≤ (n : ℝ) := hh.trans hnceil
    nlinarith [(div_le_iff₀ ha).mp hdiv]
  let i := τ ⟨0, hnN⟩
  have hi : ((classVertices τ i).card : ℝ) ≤ n := by
    exact_mod_cast (show (classVertices τ i).card ≤ n from by
      simpa only [card_univ, Fintype.card_fin] using card_le_univ (classVertices τ i))
  have ha1 : a ≤ 1 := by nlinarith [hsize i]
  have hb := vertex_deletion_bounds G τ Z ha ha1 hδ hδa hn4 hZ hsize
  have hmass : 2*δ ≤ C*δ := mul_le_mul_of_nonneg_right hC2 hδ
  have hden : 8*δ/a ≤ C*δ := by
    simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hC8 hδ
  refine ⟨fun i => (hb.2.2.1 i).trans hmass, ?_, ?_⟩
  · intro i j
    have hp := (hb.2.2.2 i j).trans hden
    refine ⟨hp, ?_⟩
    have he : (1 - deletedBlockDensity G τ Z i j) - (1 - blockDensity G τ i j) =
        -(deletedBlockDensity G τ Z i j - blockDensity G τ i j) := by ring
    rw [he, abs_neg]
    exact hp
  · intro hq hsmall
    obtain ⟨hr, hl⟩ := vertex_deletion_lambda_bound G τ Z ha ha1 hδ hδa hn4 hZ hsize hq
      (hden.trans hsmall)
    exact ⟨hr, hl.trans (mul_le_mul_of_nonneg_right hCL hδ)⟩

end HadwigerRamsey.ThomasonUpper
