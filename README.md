# Hadwiger–Ramsey

Research manuscript and Lean formalization. The original manuscript is
`hadramoct30.tex`; `thomasonupper-counterexample/` is preserved separately.

Theorem 1.4 (`thomasonlower`), the inhomogeneous random-graph upper bound
on the Hadwiger number, is fully proved in Lean.

The endpoint is `HadwigerRamsey.thomasonlower`. The kernel reports only
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
checks the proofs on pushes and pull requests. The manuscript is preserved
without edits. Other manuscript results have not yet been formalized.
