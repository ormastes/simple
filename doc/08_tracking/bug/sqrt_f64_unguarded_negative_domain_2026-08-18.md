# RESOLVED: `sqrt_f64` unguarded for negative input — returned finite garbage instead of NaN

- Filed: 2026-08-18
- Status: RESOLVED 2026-08-18
- Source: C-MIG-0029 (`src/lib/common/math/special.spl` migration unit), found
  via `test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl`.

## Defect

`sqrt_f64` (`src/lib/common/math/special.spl:445`, delegating to the private
kernel `_sqrt_f64` at line 82) is a 40-iteration Newton's-method square root.
It was NOT guarded for negative input: `sqrt_f64(-4.0)` returned
`6.070281514079917` — a finite, wrong number — while the C/Rust oracle
`rt_math_sqrt` (`src/compiler_rust/compiler/src/interpreter_extern/math.rs::
rt_math_sqrt_fn`, which calls Rust's hardware `f64::sqrt`) correctly returns
NaN for a negative radicand per IEEE 754.

Reproduced pre-fix (verbatim, via the spec's now-updated assertion, matching
the original divergence text this doc replaces):
```
sqrt_f64(-4.0) == 6.070281514079917   (finite, wrong)
rt_math_sqrt(-4.0) is NaN             (correct)
```

While investigating, two more boundary gaps were found and fixed in the same
change:
- **NaN input**: fell through to the Newton loop unguarded; happened to
  still produce NaN by IEEE propagation, but was not an explicit contract.
- **+infinity input**: the Newton loop starts at `g = x`, so for `x = +inf`
  the first iteration computes `x / g = inf / inf`, which IEEE 754 defines
  as **NaN**, not 1 — poisoning every subsequent iterate. Pre-fix,
  `sqrt_f64(+inf)` returned NaN instead of `+inf`. Verified live via a
  standalone probe before the fix landed.

## Fix

`src/lib/common/math/special.spl`, private kernel `_sqrt_f64` (around line
82): added explicit boundary guards, in order, before the Newton loop:

1. `if x != x: return _sqrt_nan()` — NaN input -> NaN.
2. `if x < 0.0: return _sqrt_nan()` — negative input -> NaN.
3. `if x == 0.0: return x` — preserves sign, so `-0.0 -> -0.0`, `+0.0 -> +0.0`
   (unchanged from before; this branch already existed).
4. `if x == pos_inf: return x` (new) — `+infinity -> +infinity`, guarded
   explicitly rather than relying on the Newton loop, because the loop
   cannot handle it (see above).

`_sqrt_nan()` is a new private helper reusing the codebase's established NaN
idiom (same pattern as `distributions.spl`'s and `financial.spl`'s existing
`_nan()`: `var big = 1.0e308; val inf = big * 10.0; inf - inf` — a literal
`0.0 / 0.0` is const-folded and rejected by the compiler, and the
interpreter traps runtime float division by zero, so NaN must come from
plain IEEE overflow instead).

The valid non-negative domain (`x >= 0`, finite, non-NaN) is **untouched** —
the Newton loop body is byte-identical to before, so results for that domain
remain bit-identical. Confirmed by the existing 100-vector shared
non-negative-domain loop in the spec passing unchanged.

## Test

`test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl`:
- REPRODUCE: header comment quotes the pre-fix divergence verbatim (see
  above); the spec's "diverges from the oracle" `it` block was flipped to
  "agrees with the oracle on negative input (NaN, post-fix)", asserting
  `simple != simple` (NaN-safe self-inequality) instead of asserting
  disagreement with the oracle.
- SIMILAR cases added in a new `it "matches the oracle on other
  domain-boundary values"` block: -0.0, +0.0, +infinity, NaN input,
  smallest negative denormal (`-4.9e-324`), -1.0 — each asserted equal to
  (or NaN-safely matching) `rt_math_sqrt`.
- Extended coverage: added a **second, separate** shared loop (`it "matches
  the oracle on a second shared loop covering the negative domain"`, 40
  seeded-LCG vectors negated, plus forced `-0.0`/`-1.0`) rather than merging
  into the existing 100-vector non-negative loop, so that loop's plain
  `_approx` equality assertion is not disturbed by NaN-safe comparison
  logic for the new negative-domain vectors.

Result (via `bin/simple run`, since `bin/simple test` currently fails to
parse an unrelated stdlib file — `src/lib/nogc_sync_mut/io/process_ops.spl`,
pre-existing on this seed binary, reproduces identically on every spec in
this directory including specs untouched by this change):
```
8 examples, 0 failures
SPEC FILE VERDICT: test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl outcome=OK declared>=8 executed=8 passed=8 failed=0 skipped=0 dropped=0
```

Other math specs re-run green and unaffected:
`special_spec.spl` (55/55), `financial_spec.spl` (76/76),
`distributions_spec.spl` (55/55), `math_spec.spl` (13/13).
`statistics_spec.spl` fails with an unrelated, pre-existing module-resolution
error (`cannot resolve import lib.math.statistics`) that does not touch
`sqrt_f64` or `special.spl` — not caused by, or related to, this change.

## Domain audit: other unguarded Newton/iteration kernels in `special.spl`

Grepped every `Domain:` docstring in `special.spl` for the same
"unguarded negative/boundary input -> should be NaN per an IEEE-like oracle"
shape as `sqrt_f64`. None of the others share the exact one-line guard
pattern (a single sign/NaN/inf check mapping straight to `_nan()`), because
each has its own, different documented "quirk" behavior instead of an
implicit assumption of finite garbage output, so none were changed:

- `gamma_ln`/`gamma_fn` (x <= 0 or negative integer poles) — Lanczos series
  evaluated with a documented, deliberate quirk output, not a raw-garbage
  Newton divergence; no oracle comparison exists in this codebase yet.
- `beta_fn` (a <= 0 or b <= 0) — same: documented quirk, not this bug's shape.
- `incomplete_beta` / `incomplete_beta_inv` (x <= 0.0, p <= 0/>= 1) —
  bisection-based (60/200-step bracket), not Newton; different failure mode
  (bracket exhaustion returning `hi`), not a one-line sign guard.
- `incomplete_gamma_p_inv` — same bisection shape as above.
- `ln_f64` (x <= 0.0) — normalization loop, not Newton; "spins or returns
  garbage" per its own docstring, different failure mode.
- `powf` (base <= 0.0) — already explicitly guarded, but deliberately
  returns 0.0 (not NaN) as a documented quirk inherited from formula.spl;
  changing it would break inherited compatibility, out of scope here.
- `factorial2` (n <= 1, including negative n) — loop-never-executes shape,
  returns 1.0, not this bug's shape.

None of these were touched. If any of them later gets an oracle-based
cross-language spec like `sqrt_f64`'s, each should be re-evaluated
individually against that oracle rather than assumed to need the same fix.

## Related, separately filed: `sqrt_f64` accuracy for extreme-magnitude input

While writing the "similar cases" boundary spec (task's fix-test standard
item 2, "largest finite value"), found that `sqrt_f64(1.7976931348623157e308)`
(f64::MAX) does **not** converge within the kernel's fixed 40 Newton
iterations: the loop starts at `g = x`, and reaching the quadratic-convergence
regime from `g / sqrt(x) = sqrt(x) ~= 1.34e154` requires roughly
`log2(1.34e154) ~= 512` halving iterations before Newton's usual doubling of
correct digits even begins. Measured live: `sqrt_f64(1.7976931348623157e308)`
returns approximately `1.63e308` (order-of-magnitude close to `x` itself, not
to the correct answer `~1.3407807929942596e154`).

This is a genuine, pre-existing accuracy limitation, independent of the
negative-domain guard fixed above — it affects only extreme-magnitude
**valid** (non-negative, finite) input, which this change's constraint ("the
100-vector shared loop must still pass unchanged", i.e. the Newton loop body
stays byte-identical) explicitly keeps untouched. Not fixed here; the spec
records the discovery (`special_sqrt_crosslang_spec.spl`, "matches the oracle
on other domain-boundary values" — the "largest finite value" block asserts
both sides are non-NaN and documents the divergence in a comment, rather than
asserting numeric agreement) instead of asserting a numeric agreement it does
not have. Left OPEN as a distinct future fix (candidate: seed the Newton
iterate from a cheap initial estimate, e.g. via bit-manipulation "fast inverse
sqrt"-style seeding or by scaling `x` into a well-conditioned range before
iterating, then rescaling — not attempted here to keep this change scoped to
the negative-domain guard).

## C-MIG-0029 inventory update

The C-MIG-0029 inventory entry's "KNOWN SEMANTIC DIVERGENCE" field for
`sqrt_f64` vs `rt_math_sqrt` on negative input is now FIXED as of this doc;
the negative-input divergence no longer exists. See the updated header
comment in `special_sqrt_crosslang_spec.spl` for the resolved-state summary
(the file previously stated the divergence as permanent/documented; that
framing is now stale and superseded by this doc).
