# Proposition 4.2: four-colour Hadwiger–Ramsey asymptotic

This development formalizes **Proposition 4.2** of *Asymptotics of the
three-color Hadwiger-Ramsey numbers* by **Sergey Norin and Neil Rahman**:
the four-colour Hadwiger–Ramsey asymptotic with its explicit leading constant.
Its proof uses [Proposition 4.1](../ComponentTransfer/README.md) of
*Asymptotics of the three-color Hadwiger-Ramsey numbers*, the component transfer theorem.

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

In the namespace `HadwigerRamsey4Col`, the public statement of Proposition 4.2 in
[Ramsey.lean](Ramsey.lean) is:

```lean
theorem theorem1_1 :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds beta4⁻¹)
```

Here `hadwigerRamsey k` is exactly $R_h(k;4)$. It is defined in the
namespace `HadwigerRamsey4Col` by:

```lean
noncomputable abbrev hadwigerRamsey (k : ℕ) : ℕ :=
  ComponentTransfer.hadwigerRamsey 4 k
```

The underlying definitions in the namespace `ComponentTransfer`, with
`HadwigerRamsey` open, are:

```lean
def IsDecomposition {r n : ℕ} (G : Fin r → SimpleGraph (Fin n)) : Prop :=
  ∀ u v, u ≠ v → ∃! c, (G c).Adj u v

def ForcesMinor (r n k : ℕ) : Prop :=
  ∀ G : Fin r → SimpleGraph (Fin n), IsDecomposition G →
    ∃ c : Fin r, HasCliqueMinor (G c) k

noncomputable def hadwigerRamsey (r k : ℕ) : ℕ :=
  sInf {n | ForcesMinor r n k}
```

`Fin n` is the vertex set $\{0,\ldots,n-1\}$, and `Fin r` indexes the
colours. The graph `G c` contains the edges of colour `c`; `∃! c` requires
exactly one colour for each pair of distinct vertices. Thus
`ForcesMinor 4 n k` says that **every** four-colouring of $K_n$ has a colour
containing a $K_k$ minor. `HasCliqueMinor` uses the branch sets described above.

`sInf` takes the infimum of these natural-number orders. The set is proved
nonempty for `r ≥ 2` using the transfer bound, so this infimum is its
**least element**. The checked results `ComponentTransfer.hadwigerRamsey_spec`
and `ComponentTransfer.hadwigerRamsey_le` establish that it forces the minor
and is no larger than any other forcing order. See
[ComponentTransfer/Ramsey.lean](../ComponentTransfer/Ramsey.lean) for the
definitions and leastness proofs, [Graph.lean](../HadwigerRamsey/Graph.lean)
for `HasCliqueMinor`, and [Ramsey.lean](Ramsey.lean) for the specialization
to four colours.

The limit says that $R_h(k;4)/(k\sqrt{\ln k})$ tends to $\beta_4^{-1}$,
which is the meaning of the displayed asymptotic formula.
`beta4_eq_of_root` proves the stated value of $\beta_4$ for every root
satisfying the specification above. `theorem1_1_explicit` substitutes that
value into the limit itself, so its leading constant is
$\bigl(\sqrt{-(3/4)\ln p}\bigr)^{-1}$.

## Proof and dependencies

The result combines two already checked theorems:

1. [Proposition 4.1](../ComponentTransfer/Asymptotic.lean) of
   *Asymptotics of the three-color Hadwiger-Ramsey numbers*,
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

The Lean component optimization proof roughly follows the arguments in
[four_colour_analytic.tex](four_colour_analytic.tex). The
[component optimization guide](ComponentOptimization.md) records the
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

The supporting optimization development formalizes Theorem 1, Lemmas 2–4,
Proposition 5, and Lemma 6 of
[four_colour_analytic.tex](four_colour_analytic.tex).
Those numbers refer to the companion source; the resulting Hadwiger–Ramsey
asymptotic is Proposition 4.2 of *Asymptotics of the three-color
Hadwiger-Ramsey numbers*. The Lean declaration name
`theorem1_1` is retained for compatibility.
The numerical estimates use Mathlib's exponential and logarithm
bounds with exact rational arithmetic.

## Verification

Run `lake build` and `python3 scripts/check_proofs.py` at the repository root.
The project uses Lean **4.33.0** and the matching Mathlib release. The root
module [HadwigerRamsey4Col.lean](../HadwigerRamsey4Col.lean) imports the main
Ramsey theorem and prints its kernel dependencies, including those of the
version with the exact constant substituted.
