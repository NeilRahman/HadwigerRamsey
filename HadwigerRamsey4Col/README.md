# Four-colour Hadwiger–Ramsey asymptotic

This development proves the four-colour analogue of Theorem 1.1 of the
Hadwiger–Ramsey manuscript, with an explicit leading constant.

## Main result

As the integer $k$ tends to infinity,

$$
R_h(k;4)=\bigl(\beta_4^{-1}+o(1)\bigr)k\sqrt{\ln k},
\qquad
\beta_4=\sqrt{-\frac34\ln p},
$$

where $p\in(0,1)$ is the unique solution of

$$
3p^6+2p-2=0.
$$

Here $R_h(k;4)$ is the least integer $n$ such that every edge colouring of
$K_n$ with four colours has a monochromatic $K_k$ minor. A $K_k$ minor
consists of $k$ nonempty, connected, pairwise disjoint vertex sets with an
edge between every two distinct sets. All logarithms are natural.

In the namespace `HadwigerRamsey4Col`, the public statement in
[Ramsey.lean](Ramsey.lean) is:

```lean
theorem theorem1_1 :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds beta4⁻¹)
```

`hadwigerRamsey k` is exactly `ComponentTransfer.hadwigerRamsey 4 k`.
The limit says that $R_h(k;4)/(k\sqrt{\ln k})$ tends to $\beta_4^{-1}$,
which is the meaning of the displayed asymptotic formula.
`beta4_eq_of_root` proves the stated value of $\beta_4$ for every root
satisfying the specification above. `theorem1_1_explicit` substitutes that
value into the limit itself, so its leading constant is
$\bigl(\sqrt{-(3/4)\ln p}\bigr)^{-1}$.

## Proof and dependencies

The result combines two already checked theorems:

1. [Component transfer Theorem 5](../ComponentTransfer/Asymptotic.lean),
   `ComponentTransfer.theorem5`, proves the Ramsey asymptotic for every
   fixed number of colours $r\ge2$, with the reciprocal of the component
   program's optimum as its leading constant.
2. [The four-colour optimum](Theorem1.lean), `beta4_eq` and `theorem1`,
   evaluates that program at $r=4$:
   $\beta_4^2=-(3/4)\ln p$. It also proves that the infimum is attained.

`Ramsey.lean` specializes the first theorem to four colours and substitutes
the exact constant from the second. Both ingredients are unconditional
Lean proofs, and both are included in the default repository build.

## Supporting component optimization

The [component optimization guide](ComponentOptimization.md) records the
numbered lemmas, proof details, and reused Mathlib results.

The program uses positive atom masses summing to one, four component
partitions, and symmetric colour densities in $[0,1)$ summing to one on
every ordered pair. A colour's density vanishes between different parts of
its partition. Component entropy includes diagonal terms, and the objective
is the square root of the largest component entropy. `beta4` is defined as
`ComponentTransfer.beta 4`, the infimum of this objective over all finite
instances.

[AttainingConstruction.lean](AttainingConstruction.lean) checks the attaining
instance explicitly: four masses $1/4$, partitions

$$
\{12,34\},\qquad\{13,24\},\qquad\{14,23\},\qquad\{1234\},
$$

diagonal densities $(1/3,1/3,1/3,0)$, and, on each distinct pair, density
$p$ in its unique pairing colour and $1-p$ in the fourth colour.

The lower bound applies to every finite component instance, with no
restriction on its number of atoms or component pattern. Its main steps are:

- Merge identical component-label words using logarithmic Jensen bounds
  ([MergingEntropy.lean](MergingEntropy.lean)).
- Classify the resulting words into two fixed coordinates, a radius-one
  Hamming ball, or the four-atom pairing pattern
  ([Patterns.lean](Patterns.lean)).
- Exclude the first two cases using the checked capacity bounds
  ([FixedPattern.lean](FixedPattern.lean), [BallExclusion.lean](BallExclusion.lean),
  and [Lemma6.lean](Lemma6.lean)).
- Apply the four-atom stability and dual bounds to the surviving pattern
  ([Lemma5.lean](Lemma5.lean), [TriangleReduction.lean](TriangleReduction.lean)).

This also formalizes Theorem 1, Lemmas 2–4, Proposition 5, and Lemma 6 of
`four_colour_analytic.tex`; the local manuscript is excluded from version
control. The numerical estimates use Mathlib's exponential and logarithm
bounds with exact rational arithmetic.

## Verification

Run `lake build` and `python3 scripts/check_proofs.py` at the repository root.
The project uses Lean **4.33.0** and the matching Mathlib release. The root
module [HadwigerRamsey4Col.lean](../HadwigerRamsey4Col.lean) imports the main
Ramsey theorem and prints its kernel dependencies, including those of the
version with the exact constant substituted.
