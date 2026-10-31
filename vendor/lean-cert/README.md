# LeanCert interval-analysis subset

Source: https://github.com/alerad/leancert/tree/122a3776fe157f92ee8a1116faf079378bcf18af

The six `LeanCert/Core/**/*.lean` files are copied from this exact commit.
They provide rational interval arithmetic, exponential Taylor bounds, and
logarithm bounds via argument reduction and the atanh series. The original
file headers and upstream LICENSE are preserved. The upstream LICENSE is
AGPL-3.0; the upstream source headers themselves say Apache 2.0. These
notices are recorded as supplied, without changing either.

Two proof-script changes in `Core/Taylor.lean` adapt the source to the
project's Lean/Mathlib v4.24.0:

- Remove a redundant `ring` after `field_simp` in the Taylor remainder proof.
- Replace the final `ring_nf` by `push_cast; ring` in the logarithm
  iterated-derivative proof.

One documentation sentence about placeholders has been reworded for the
project's conservative source guard. No theorem statement or interval
algorithm has been changed. `LeanCert.lean` is a local import entry point.

The subset is now checked with Lean/Mathlib **v4.33.0**. Compatibility edits
for that release retain every upstream theorem statement and interval algorithm:

- `Core/Expr.lean`: use an explicit positive-multiplication lemma in the
  monotonicity proof.
- `Core/IntervalRat/LogReduction.lean`: use the renamed `Nat.cast_natAbs` lemma.
- `Core/IntervalRat/Taylor.lean`: update the exponential-bounds import path
  and make definitional function/cast equalities explicit for the new elaborator.
  Use `convert!` in the series proof to unfold equivalent algebra instances.
- `Core/Taylor.lean`: import hyperbolic derivatives explicitly, adapt smoothness
  arguments to the new nonzero-order interface, and wrap Mathlib's generalized
  unordered-interval Taylor theorem to recover the original ordered-interval
  interface. Obsolete auxiliary order calculations are removed.

Only this subset is compiled. The full LeanCert tactic/plugin machinery is
not used. `HadwigerRamsey/FOpt/Interval.lean` supplies a small expression
checker, outward rounding, and their soundness proofs. Numerical checks
use `decide +kernel`, not native evaluation as a logical premise. The
endpoint's printed dependency report is checked alongside all other proofs.
