# Hadwiger–Ramsey

Lean formalization of the three-colour and four-colour Hadwiger–Ramsey
asymptotics, together with the general component transfer theorems.

The project uses Lean **4.33.0** and the matching Mathlib release. Both local
builds and GitHub Actions read the version from `lean-toolchain`.

## The main result

**Theorem 1.1.** The three-colour Hadwiger–Ramsey number satisfies

$$
R_h(k;3)=\bigl(\beta^{-1}+o(1)\bigr)k\sqrt{\ln k},
\qquad
\beta=\frac12\sqrt{-\ln(10-4\sqrt6)}.
$$

Here $R_h(k;3)$ is the least integer $n$ such that every colouring of the
edges of $K_n$ with three colours has a monochromatic $K_k$ minor.
A $K_k$ minor consists of $k$ nonempty, connected, pairwise disjoint
vertex sets with an edge between every two distinct sets.

In the namespace `HadwigerRamsey`, the public Lean statement is:

```lean
theorem theorem1_1 :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds beta⁻¹)
```

`hadwigerRamsey k` is the least vertex count with the stated forcing
property. `Filter.Tendsto` says that its ratio to $k\sqrt{\ln k}$ tends to
$\beta^{-1}$ as the integer $k$ tends to infinity; this is exactly the
meaning of the displayed asymptotic formula. The proof in
[Ramsey.lean](HadwigerRamsey/Ramsey.lean) deduces this limit from the
checked Theorems 1.2 and 1.3, with integer rounding and the change from
$\ln n$ to $\ln k$ made explicit.

## Four colours

The [four-colour development](HadwigerRamsey4Col/README.md) resolves the
asymptotics of the four-colour Hadwiger–Ramsey numbers:

$$
R_h(k;4)=\bigl(\beta_4^{-1}+o(1)\bigr)k\sqrt{\ln k},
\qquad
\beta_4=\sqrt{-\frac34\ln p},
$$

where $p\in(0,1)$ is the unique root of $3p^6+2p-2=0$. The main Lean
theorem is `HadwigerRamsey4Col.theorem1_1`.

This result is proved through the
[component transfer theorem](ComponentTransfer/README.md), which relates
Hadwiger–Ramsey asymptotics to a finite component optimization problem.
Combining that theorem with the exact four-colour component optimum gives
the constant above. The optimum is attained by four equal masses with
three pairing partitions and one spanning partition. The component
transfer and optimization proofs are both checked in Lean and included
in the default local and GitHub Actions build.

## Supporting results and scope

Theorem 1.2 is proved as `HadwigerRamsey.existencethm`,
for every sufficiently large integer order, including odd orders.
It constructs a three-colour decomposition with each Hadwiger number at
most `(1+epsilon)*beta*n/sqrt(log n)`, using Theorem 1.4 explicitly.
The entry module is `HadwigerRamsey/Existence.lean`.

Theorem 1.3 is proved as `HadwigerRamsey.mainthm` in
`HadwigerRamsey/Main.lean`, following the manuscript's proof.
It explicitly uses Lemmas 3.2, 3.3, 3.5, and 3.6,
Theorem 1.5, and Corollary 3.9; the build checks those dependencies.
It does not directly invoke Corollary 3.4: its trimming
and unequal-part minor helpers effectively re-prove that corollary.

Corollary 3.4 is proved as `HadwigerRamsey.unequalBipMinor` in
`HadwigerRamsey/UnequalBipMinor.lean`. It extends Lemma 3.3 to
`|B| >= |A| >= n₀`, with density at least `1-gamma` and the bound
`K*|A|/sqrt(log |A|)`. It reuses the existing trimming helper and the
same constants supplied by Lemma 3.3.

Theorem 1.4, the inhomogeneous random-graph upper bound
on the Hadwiger number, is fully proved in Lean.

Lemma 3.5 is proved as `HadwigerRamsey.denseMinor` in
`HadwigerRamsey/DenseMinor.lean`, explicitly using Lemma 3.3.
A deterministic missing-edge estimate replaces the random balanced-cut
argument, with a smaller auxiliary density error and a larger cutoff.

Lemma 3.3 is proved as `HadwigerRamsey.bipMinor` in
`HadwigerRamsey/BipMinor.lean`. It explicitly applies Theorem 1.5 to a
large core of a dense balanced bipartite graph; the statement matches the
manuscript. The auxiliary constants and pruning
argument differ as detailed in the guide.

Lemma 3.1, for a nonempty ground set, is also proved as
`HadwigerRamsey.bigset`; see the guide for the empty-set boundary condition.

Lemma 3.2 is proved as `HadwigerRamsey.connectedsets` in
`HadwigerRamsey/ConnectedSets.lean`, following the
manuscript's splitting, absorption, merging, and separator-trimming argument.
The six controlled-partition conditions are explicit in
`ControlledPartition.Controlled`.

Lemma 3.6 is proved as `HadwigerRamsey.twobigsets` in
`HadwigerRamsey/TwoBigSets.lean`. Its proof explicitly obtains controlled
partitions from Lemma 3.2, applies Lemma 3.1, and applies Lemma 3.3
to the remaining colour. The build checks these theorem dependencies.

Lemma 3.7 is proved as `HadwigerRamsey.fopt`; its alternative
cubic-bound proof and endpoint convention are described in the guide.

Lemma 3.8 is proved as `HadwigerRamsey.opt`. Its symbolic proof reuses
Lemma 3.7 and Mathlib, with a stronger helper allowing zero weights and
one-sided mass constraints.

Corollary 3.9 is proved as `HadwigerRamsey.optapprox`, with closed
parameter bounds and δ > 0. Its proof explicitly depends on Lemma 3.8 through
positive-support restriction and probability rescaling, followed by
compactness. The build checks that theorem dependency.

Theorem 1.5 is fully proved as `HadwigerRamsey.thomasonupper` in
`HadwigerRamsey/ThomasonUpper.lean`. Its statement has the exact ordered
double sum, capped densities, and additive error outside the square root.
The appendix development is in `HadwigerRamsey/ThomasonUpper/`, including
Lemma A.1, vertex-deletion stability (Lemma A.2), the uniform complete-family
consequence of Corollary A.3, random reservoirs, and the final clique-minor
construction.
The Menger step uses the existing public finite vertex-Menger proof
vendored in `vendor/menger/`.

**Corollary A.3 has a weaker standalone conclusion in Lean:** the proved
complete-family result supplies the required disjoint sets, edges between
distinct sets, part-count bounds, and maximum part-size bound, but does
not assert that they cover the original graph or have globally balanced
sizes. Theorem 1.5 uses only the proved properties and has its full stated
conclusion. All numbered main-text claims are formalized; see the guide
for this appendix distinction and the other stated technical conventions.

The endpoints use only the standard classical foundations. The kernel reports only
`propext`, `Classical.choice`, and `Quot.sound`.
See [FORMALIZATION.md](FORMALIZATION.md) for the exact statement and paper-to-Lean map.

## Checking the Lean project

Install [elan](https://github.com/leanprover/elan), then run:

```sh
source "$HOME/.elan/env"
lake exe cache get
python3 scripts/check_proofs.py
lake build
```

Lean, Mathlib, and transitive dependencies are pinned. GitHub Actions
checks the proofs on pushes and pull requests.
