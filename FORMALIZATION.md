# Formalization status

Theorem 1.4 (`thomasonlower`) of `hadramoct30.tex` is proved in Lean 4.
The endpoint is `HadwigerRamsey.thomasonlower` in
`HadwigerRamsey/ThomasonLower.lean`.

Lemma 3.1 (`bigset`) is also proved, for a nonempty ground set, as
`HadwigerRamsey.bigset` in `HadwigerRamsey/BigSet.lean`.

## Exact meaning of the endpoint

For each positive real ε, the theorem supplies a natural cutoff n₀ before
quantifying over n, the number of classes k, the partition, the symmetric
probability matrix, or the probability space. Thus the cutoff is uniform
in all of those data, as required in the manuscript.

Vertices are `Fin n`. A class map `τ : Fin n → Fin k` represents the
partition. `classMass τ i` is the cardinality of its fiber divided by n;
`blockLambda τ p` is precisely the manuscript's double sum of
`αᵢ αⱼ (-log (1-pᵢⱼ))`. Its square root is L. Empty classes are allowed,
which only strengthens the result and leaves their contribution zero.

The random graph is `G : Ω → SimpleGraph (Fin n)` on any probability
space. The assumptions require measurable, mutually independent
undirected edge events, with probabilities `p (τ u) (τ v)`. Independence
is Mathlib's `ProbabilityTheory.iIndepSet`, not a substitute definition or
an assumed bound on partitions. It is enough to specify increasing pairs
of vertices because graphs are undirected. This formulation applies to
the independent-edge random graph of the manuscript without committing
to one particular construction of its sample space.

`HasCliqueMinor G s` uses pairwise disjoint connected branch sets and an
edge between every distinct pair. Connectedness is Mathlib's induced-graph
`SimpleGraph.Connected`, including nonemptiness. `hadwigerNumber` is the
maximum possible minor order. The graph module proves that the maximum
is attained and that having a clique minor of order s is equivalent to
`s ≤ hadwigerNumber G`. No connection to an alternative graph-minor API
is needed for this branch-set definition.

The conclusion is the manuscript's real-valued probability inequality:
the probability of `hadwigerNumber G ≤ (1+ε) L n / sqrt(log n)` is at
least `1-ε`. Logarithms are natural. The case ε ≥ 1 is covered directly
by nonnegativity of probability.

## Paper-to-Lean map

| Manuscript ingredient | Lean declaration / module |
| --- | --- |
| Minor gives permissible partition (`obs:minor-partition`) | `HasCliqueMinor.permissible`, `Graph.lean` |
| Hadwiger number and branch-set meaning | `hadwigerNumber`, `hasCliqueMinor_iff_le_hadwigerNumber`, `Graph.lean` |
| Total-weight identity (`lem:total-weight`) | `total_weight_identity`, `Weights.lean` |
| Disjoint block pairs use independent edges | `probability_allHits`, `Probability.lean` |
| Probability of no edge across a block pair | `probability_noHit`, `Probability.lean` |
| Finite Jensen and exponential product estimate | `sum_exp_neg_ge`, `permissible_product_bound`, `Analytic.lean` |
| Fixed-partition bound (`lem:fixed-partition`) | `fixed_partition_bound`, `Finite.lean` |
| Union bound (`cor:finite`) | `finite_minor_bound`, `Finite.lean` |
| Uniform asymptotics (`lem:uniform-decay`) | `uniform_tail_bound`, `Asymptotic.lean` |
| Block average equals vertex-pair average | `blockLambda_identity`, `Blocks.lean` |
| Measurability of finite graph properties | `measurableSet_graph_property`, `Measurability.lean` |
| Theorem 1.4 (`thomasonlower`) | `thomasonlower`, `ThomasonLower.lean` |
| Lemma 3.1 (`bigset`), nonempty ground set | `bigset`, `BigSet.lean` |

The finite probability result is slightly more general: logarithmic
weights may vary independently on every potential edge. The final
wrapper specializes it to the block probabilities and the exact L in
the manuscript. The rounding argument uses `ceil R`; excluding a minor
of that order gives `hadwigerNumber < R`, which implies the stated weak
inequality, including when R is an integer.

## Verification

Pinned Lean: `leanprover/lean4:v4.24.0`.
Pinned Mathlib: tag `v4.24.0`, commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
All transitive dependencies are recorded in `lake-manifest.json`.

Run:

```sh
source "$HOME/.elan/env"
lake exe cache get
python3 scripts/check_proofs.py
lake build
```

The root module prints the endpoint's kernel axiom dependencies. The
expected list is exactly `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or project-defined axioms. GitHub Actions
repeats the build and source guard on pushes and pull requests.

The original manuscript and existing counterexample notes are preserved
without edits. The mathematical correspondence above is documented for
human review; kernel checking establishes the Lean statement.

## Lemma 3.1: two partitions (`bigset`)

The endpoint `HadwigerRamsey.bigset` uses Mathlib's existing
`Finpartition s` directly, for a finite set `s`. It assumes `s.Nonempty`,
that each partition has at most k parts, and ε > 0. It proves exactly the
stated alternatives: a part of either partition has size at least
(1−ε)|s|, or there are A and B of size at least ε|s|/k² lying in distinct
parts of both partitions. The subsets are chosen as intersections of
parts; no new partition notion is introduced.

**Boundary condition:** the manuscript does not explicitly require n > 0.
With the usual definition of partitions into nonempty parts, its literal
statement fails for n = 0: both partitions are empty, so neither outcome
can supply the required parts. The Lean theorem makes the nonemptiness
condition explicit. It implies k > 0 from the partition-size bound, so
no separate positivity assumption on k is needed. This is the version
used by the later application to a large vertex set. The manuscript has
not been edited.

The proof follows the manuscript. Large intersection cells cannot differ
in both their row and column if the second outcome fails. A short logical
helper, `supported_on_row_or_column`, shows that all such cells then lie
in one row or one column, also handling the case of no large cells.
`large_part_of_small_other_intersections` bounds the total size outside
that row/column. It reuses Mathlib's partition disjointness and coverage,
`Finpartition.sum_card_parts`, `Finset.card_biUnion`, and finite sum/cardinality
inequalities. `sum_card_inter_parts` packages the intersection-counting
identity needed by this argument.

A targeted public search and a search of the pinned Mathlib sources found
finite-partition and pigeonhole infrastructure, rather than an existing
copy of this exact lemma. The reusable partition API is
[Mathlib.Order.Partition.Finpartition](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Order/Partition/Finpartition.lean)
(by Yaël Dillies and Bhavik Mehta). Mathlib's weighted pigeonhole results
were also inspected; direct finite sums suffice here. `BigSet.lean` is new
project code; the underlying finite-partition implementation is reused
without modification.

Both endpoints have an axiom report in the root module and are included
in the same build and source guard.

## Related formalizations and reused results

Search performed on 31 October 2026. Targeted searches for the paper's
title, authors, random clique minors, and permissible partitions did not
locate a complete existing formalization of the Bollobás–Catlin–Erdős
result. This is a search outcome, not a claim that none exists.

- [Bollobás, Catlin, and Erdős (1980), original paper](https://users.renyi.hu/~p_erdos/1980-10.pdf):
  the homogeneous permissible-partition upper-bound argument is on pages
  196–197; the fixed-p extension is stated on page 198. This is the
  mathematical source, not a Lean dependency.
- [uw-math-ai/random_graphs](https://github.com/uw-math-ai/random_graphs):
  an Erdős–Rényi random-graph formalization project. Its README also links
  earlier work by Yael Dillies. It was located as related infrastructure;
  no source from it is vendored or assumed here.
- [snorin239/LinearHadwiger](https://github.com/snorin239/LinearHadwiger):
  a related Lean formalization about coloring and clique minors. Its main
  result is different from this random-graph upper bound. It is not a
  dependency of this project.
- [Mathlib finite Jensen](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Analysis/Convex/Jensen.lean):
  `convexOn_exp.map_sum_le` is reused directly.
- [Mathlib independence](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Probability/Independence/Basic.lean):
  the proof reuses `iIndepSet_iff` and
  `iIndepSet.indep_generateFrom_of_disjoint`, along with measurable
  generated events and the measure-of-intersection product identity.
- [Mathlib power/logarithm asymptotics](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean):
  `isLittleO_log_rpow_rpow_atTop` supplies the growth estimates.
- Mathlib also provides finite union bounds, exponential/logarithm and
  square-root identities, ceilings, finite sums, and graph connectivity.

No third-party Lean source was copied into this repository.
