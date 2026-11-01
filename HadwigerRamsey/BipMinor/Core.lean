import HadwigerRamsey.BipMinor.Connectivity

open scoped Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey.BipMinor
set_option maxHeartbeats 800000

attribute [-instance] SimpleGraph.instDecidableComapAdj in
/-- A dense balanced bipartite graph has a large core with high minimum
degree, positive class masses, and almost complete cross density. -/
theorem exists_core {n a : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (ha : 100 ≤ a) (hp : ∀ u v, G.Adj u v → c u ≠ c v)
    (hsize : ∀ i, (classVertices c i).card = a) {gamma : ℝ}
    (hg : 0 ≤ gamma) (hgsmall : gamma ≤ 1/128)
    (hedges : (1-gamma)*(a : ℝ)^2 ≤ G.edgeFinset.card) :
    ∃ Z : Finset (Fin n), Z.card < n ∧ a ≤ n-Z.card ∧ n-Z.card ≤ 2*a ∧
      (∀ u v, (restrictedGraph G Z).Adj u v → restrictedClasses c Z u ≠ restrictedClasses c Z v) ∧
      (∀ i, (classVertices (restrictedClasses c Z) i).card ≤ a) ∧
      (∀ v, 3*(a : ℝ)/4 ≤ (restrictedGraph G Z).degree v) ∧
      (∀ i, 1/4 ≤ classMass (restrictedClasses c Z) i) ∧
      1-129*gamma ≤ blockDensity (restrictedGraph G Z) (restrictedClasses c Z) 0 1 := by
  have haN : 0 < a := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast haN
  have ha100 : (100 : ℝ) ≤ a := by exact_mod_cast ha
  have hn := order_eq c hsize
  let Z := univ.filter (fun v => (G.degree v : ℝ) < 7*(a : ℝ)/8)
  have hZ := low_degree_vertices_small G c haN hp hsize hedges
  change (Z.card : ℝ) ≤ 16*gamma*a at hZ
  have hZa : (Z.card : ℝ) ≤ (a : ℝ)/8 := by
    have hh := mul_le_mul_of_nonneg_right hgsmall haR.le
    nlinarith only [hZ,hh]
  have hZaN : 8*Z.card ≤ a := by
    have hh : 8*(Z.card : ℝ) ≤ a := by linarith only [hZa]
    exact_mod_cast hh
  have hZn : Z.card < n := by omega
  have hNlo : a ≤ n-Z.card := by omega
  have hNhi : n-Z.card ≤ 2*a := by omega
  have hNp : (0 : ℝ) < ((n-Z.card : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n-Z.card)
  refine ⟨Z,hZn,hNlo,hNhi,fun u v huv => hp _ _ huv,?_,?_,?_,?_⟩
  · intro i
    have hc := congrArg card (image_restricted_class c Z i)
    rw [card_image_of_injective _ (survivorMap_injective Z)] at hc
    rw [hc]
    exact (card_le_card sdiff_subset).trans (hsize i).le
  · intro v
    have hv := survivorMap_not_mem Z v
    have hvdeg : 7*(a : ℝ)/8 ≤ G.degree (survivorMap Z v) := by
      simpa only [Z,mem_filter,mem_univ,true_and,not_lt] using hv
    have hh : (G.degree (survivorMap Z v) : ℝ) ≤ (restrictedGraph G Z).degree v+Z.card := by
      exact_mod_cast restriction_degree G Z v
    linarith only [hvdeg,hh,hZa]
  · intro i
    change 1/4 ≤ ((classVertices (restrictedClasses c Z) i).card : ℝ)/((n-Z.card : ℕ) : ℝ)
    apply (le_div_iff₀ hNp).mpr
    have hc := congrArg card (image_restricted_class c Z i)
    rw [card_image_of_injective _ (survivorMap_injective Z)] at hc
    have hh : (a : ℝ) ≤ (classVertices c i \ Z).card+Z.card := by
      have h := card_le_card_sdiff_add_card (s := classVertices c i) (t := Z)
      rw [hsize i] at h
      exact_mod_cast h
    have hNhiR : (((n-Z.card : ℕ) : ℝ)) ≤ 2*(a : ℝ) := by exact_mod_cast hNhi
    rw [hc]
    linarith only [hh,hZa,hNhiR]
  · have hdelta : 0 ≤ 8*gamma := by positivity
    have hdeltaSmall : 8*gamma < (1/2:ℝ)/2 := by linarith only [hgsmall]
    have hn4 : 4 ≤ (1/2:ℝ)*n := by rw [hn]; push_cast; linarith only [ha100]
    have hZbound : (Z.card : ℝ) ≤ (8*gamma)*n := by
      have hnR : (n : ℝ) = 2*(a : ℝ) := by exact_mod_cast hn
      rw [hnR]
      nlinarith only [hZ]
    have hs : ∀ i, (1/2:ℝ)*n ≤ (classVertices c i).card := by
      intro i; rw [hsize i,hn]; push_cast; linarith only []
    have hb := vertex_deletion_bounds G c Z (by norm_num : (0:ℝ)<1/2) (by norm_num) hdelta hdeltaSmall hn4 hZbound hs
    have hden : (0 : ℝ) < (a : ℝ)^2 := sq_pos_of_pos haR
    have horig : 1-gamma ≤ blockDensity G c 0 1 := by
      rw [cross_density G c hp hsize]
      exact (le_div_iff₀ hden).mpr hedges
    have hh := (abs_le.mp (hb.2.2.2 0 1)).1
    rw [restrictedBlockDensity]
    linarith only [hh,horig]
end HadwigerRamsey.BipMinor
