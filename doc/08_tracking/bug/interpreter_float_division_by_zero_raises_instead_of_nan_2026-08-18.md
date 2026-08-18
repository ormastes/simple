# Interpreter float division `0.0 / 0.0` raises instead of producing NaN

- Status: BLOCKED-ON-DEPLOY (fix committed to source, not yet in the deployed binary)
- Found: 2026-08-18, while writing C-MIG-0033 (`test/01_unit/lib/common/numeric_round_is_nan_crosslang_spec.spl`)
- Severity: correctness divergence from IEEE 754

## Fix (2026-08-18)

Root cause located: `src/compiler_rust/compiler/src/interpreter/expr/ops.rs`,
`BinOp::Div` arm (~line 851, pre-fix). The `use_f32` and `use_float` branches
checked `if r == 0.0 { raise "division by zero" }` unconditionally, before
knowing the numerator — the exact type-blind defect shape predicted in the
original root-cause note. Both float branches were rewritten to just perform
the division and let Rust's native `f32`/`f64` division produce IEEE 754
NaN/inf directly (no zero-check at all), while the integer branch a few lines
below (`right_val.as_int()? == 0`) is untouched and still raises. `BinOp::Mod`
was deliberately left as-is (raises on float `%` by zero too) — out of scope
for this bug, which is specifically about `/`.

Both the JIT (`SIMPLE_JIT_STRICT=1 bin/simple run`, which falls back to the
interpreter on unsupported ops) and the plain interpreter path go through this
same `ops.rs` site — both lanes were raising identically before the fix and
both produce correct IEEE results after it, confirmed on a locally-built
binary (see below).

**Deploy status:** the deployed `bin/simple` is the Rust seed and Stage 3
self-host is currently blocked (see `.claude/rules/bootstrap.md`), so this
source fix cannot take effect for the deployed binary yet. Verified instead on
a from-scratch Rust build under a dedicated `CARGO_TARGET_DIR` on `/mnt/data`
(not `bin/release/**`, per the seed-sibling-refresh procedure in
`.claude/rules/bootstrap.md`):

```
# before (deployed seed, and pre-fix local build): 0.0/0.0, 1.0/0.0, -1.0/0.0, 0.0/-0.0
error[E2001]: division by zero

# after (locally built fixed binary):
NaN
inf
-inf
NaN

# integer division by zero (5 / 0), before AND after — unchanged:
error[E2001]: division by zero
```

Regression spec: `test/01_unit/lib/common/interpreter_float_division_by_zero_ieee_spec.spl`
— 6 examples, all pass on the locally-built fixed binary
(`Results: 6 total, 6 passed, 0 failed`), all 6 FAIL on the currently deployed
seed (`Results: 6 total, 0 passed, 6 failed`), confirming this is genuinely
blocked on redeploy, not a false positive. The spec's own header carries the
same before/after evidence. Do not weaken or skip it; it should go green
automatically once a rebuilt seed/self-hosted binary carrying this fix is
deployed.

## Follow-up: C-MIG-0033 workaround in `src/lib/common/numeric_round.spl`

Not changed by this bug fix (task explicitly scoped this out — record only).
`test/01_unit/lib/common/numeric_round_is_nan_crosslang_spec.spl` currently
constructs NaN via `(0.0 - pos_inf) + pos_inf` instead of `0.0 / 0.0` to route
around this defect. Once a compiler build with this fix is deployed, that
workaround can be simplified back to `0.0 / 0.0` directly (both are
canonically NaN under IEEE 754; the indirect construction was only needed to
dodge the interpreter's prior division-by-zero raise). Left as a follow-up,
not done here, to keep this change narrowly scoped to the interpreter fix.

## Repro

```
val x = 0.0 / 0.0
```

Under `bin/simple test` (tree-walk interpreter), this raises
`semantic: division by zero` and aborts the example instead of producing
`f64::NAN`, which is what IEEE 754 float division specifies and what the
`rt_math_is_nan` C/Rust oracle (`f64::is_nan`, backed by hardware division)
would receive as input if it ever performed this division itself.

Directly observed: `bin/simple test
test/01_unit/lib/common/numeric_round_is_nan_crosslang_spec.spl` failed with
`semantic: division by zero` on both the "domain-boundary values" example and
the 100-vector bulk-loop example, both of which used `0.0 / 0.0` as a second
NaN-construction path (alongside `pos_inf - pos_inf`). Removing that one
construction and replacing it with `(0.0 - pos_inf) + pos_inf` (also
canonically NaN, via inf + -inf, which does not go through the zero-divisor
special case) made the spec pass cleanly (5 examples, 5 passed).

## Root cause (not yet located)

Whatever implements the interpreter's binary `/` operator for float operands
appears to special-case a literal/runtime zero divisor and raise a semantic
error unconditionally, rather than checking whether the numerator is also
zero (which is the IEEE 754 NaN case) versus non-zero (which is the correctly
signed-infinity case). Both cases are being routed to the same "division by
zero" error path when the divisor is `0.0`, when only some integer-domain
callers actually want that behavior.

## Impact

Any pure-Simple code relying on IEEE 754 float semantics for `x / 0.0` (NaN
when `x == 0.0`, signed infinity otherwise) gets an interpreter panic/error
instead. This is a real semantic gap between the interpreter and hardware
float division, distinct from and additional to the already-tracked
run-vs-test JIT/interpreter divergence family
(`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`).

## Unblock condition

Locate the float `/` operator's zero-divisor handling (likely in the
tree-walk interpreter's binary-op evaluation, not in `interpreter_extern`)
and make it match IEEE 754: `0.0 / 0.0` -> NaN, nonzero `/ 0.0` -> signed
infinity, never a semantic error, for float operands specifically (integer
division by zero legitimately stays an error).

## Regression coverage

`test/01_unit/lib/common/numeric_round_is_nan_crosslang_spec.spl` documents
the workaround inline but does NOT assert the correct IEEE 754 behavior
(doing so would currently fail). A follow-up spec asserting `0.0 / 0.0`
produces NaN (not an error) should be added once this is fixed, and this doc
updated to RESOLVED with that spec cited.
