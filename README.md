# Hadwiger–Ramsey

Lean formalization of results from the local research manuscript
`hadramoct30.tex`. That manuscript and local counterexample notes are
excluded from version control.

The project uses Lean **4.33.0** and the matching Mathlib release. Both local
builds and GitHub Actions read the version from `lean-toolchain`.

Theorem 1.4 (`thomasonlower`), the inhomogeneous random-graph upper bound
on the Hadwiger number, is fully proved in Lean.

Lemma 3.1 (`bigset`), for a nonempty ground set, is also proved as
`HadwigerRamsey.bigset`; see the guide for the empty-set boundary condition.

Lemma 3.6 (`fopt`) is proved as `HadwigerRamsey.fopt`; its alternative
cubic-bound proof and endpoint convention are described in the guide.

Lemma `opt` is proved as `HadwigerRamsey.opt`. Its symbolic proof reuses
`fopt` and Mathlib, with a stronger helper allowing zero weights and
one-sided mass constraints.

Corollary `optapprox` is proved as `HadwigerRamsey.optapprox`, with closed
parameter bounds and δ > 0. Its proof explicitly depends on `opt` through
positive-support restriction and probability rescaling, followed by
compactness. The build checks that theorem dependency.

Theorem 1.5 (`thomasonupper`), using the October 31 manuscript, is fully
proved as `HadwigerRamsey.thomasonupper` in
`HadwigerRamsey/ThomasonUpper.lean`. Its statement has the exact ordered
double sum, capped densities, and additive error outside the square root.
The appendix development is in `HadwigerRamsey/ThomasonUpper/`, including
A.1, vertex-deletion stability, the uniform complete-family consequence
of A.3, random reservoirs, and the final clique-minor construction.
The Menger step uses the existing public finite vertex-Menger proof
vendored in `vendor/menger/`.

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
checks the proofs on pushes and pull requests. The manuscript stays local
and is preserved without edits. Other manuscript results have not yet been formalized.
