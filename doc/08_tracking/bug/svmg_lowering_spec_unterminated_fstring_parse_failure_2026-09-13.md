# `test/01_unit/compiler/backend/svmg_lowering_spec.spl` fails to parse: "Unterminated f-string"
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Found by: BUGFIX-13 lane, while re-verifying
  `doc/08_tracking/bug/svmg_d4_lowering_deferred_subset_2026-08-07.md`'s own
  verification command.
- Severity: HIGH for this one file (the spec cannot run at all — zero
  examples execute), low blast radius (only this file confirmed affected so
  far).

## Symptom

```
bin/simple test test/01_unit/compiler/backend/svmg_lowering_spec.spl --no-session-daemon
```

fails at COMPILE time, before any example runs:

```
error: compile failed: parse: in ".../svmg_lowering_spec.spl": Unexpected
token: expected expression, found Error("Unterminated f-string")
error: test-runner: no examples executed
SPEC FILE VERDICT: ... outcome=ERROR declared>=1 executed=0 passed=0
failed=1 dropped=1 unrun=1 reason=parse-error
```

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (deployed seed,
hand-linked from `/home/yoon/dev/simple/bin/simple`, 2026-09-13).

## What was ruled out

- The error has no line/column in its message, so exact isolation was not
  completed in the time budget for this pass.
- The file's only line combining a quote and a brace (line 339,
  `value: "x={0}", interpolations: [interp]`) reproduces CLEAN in isolation:
  ```
  fn main():
      val s = "x={0}"
      print s
  ```
  prints `x=0` correctly on the same binary — no interpolation/lexer defect
  in that exact snippet alone.
- Total `{`/`}` count across the whole 408-line file is balanced (7/7), so
  it is not a simple brace-imbalance typo.
- Every line's `"` count is even (no naive unterminated-string typo per
  line); the "f-string" wording in the error suggests the interpolation
  lexer specifically, triggered by some cross-line or cross-expression
  interaction not yet isolated (candidate: the multi-line `use ...{...}`
  import block at lines 26-29 with a trailing comma before the closing
  `}` on its own line, immediately preceding the file's only interpolated
  string a few sections later — not confirmed, just the remaining
  candidate after the above eliminations).

## Repro

```
bin/simple test test/01_unit/compiler/backend/svmg_lowering_spec.spl --no-session-daemon
```

## Impact

Blocks re-verifying `svmg_d4_lowering_deferred_subset_2026-08-07`'s own
documented verification command — that bug's claimed "fails fast with a
diagnostic naming the gap" state cannot currently be re-confirmed because
the spec itself never reaches the lowering pass under test.

## Unblock condition

Isolate the exact triggering construct (bisect by extracting progressively
smaller *syntactically complete* fragments — not naive `head -N`, which
produces spurious errors of its own from truncated blocks) and file the
root cause against the lexer/parser (`src/compiler/10.frontend/core/lexer*.spl`
or the interpolation-scanning code specifically).


## Addendum 2026-11-13 — lane p3-comp1 (worktree p3comp1-wt, branch work/p3-compiler-p1-20261113)

Verdict: **parse failure FIXED at tip; one residual RED example found and fixed in-lane.**

- Repro on the tracked seed (`bin/simple.exe` @ 46fe8f6b6def): the spec now
  compiles and executes all 75 declared examples (74/75 on first re-run).
- Residual: `rejects REM on float operands instead of silently emitting the
  integer REM opcode` failed because `expect_to_equal(binop(Mod, float, float),
  float)` hit the "mixed integer/float expect operands" diagnostic — factually
  wrong, both operands are float. Root cause: `expr_is_float`
  (`src/compiler/70.backend/svmg_lowering.spl`) is opcode-support based and
  reports float REM/bitwise/shift expressions as non-float.
- Fix (this lane, `src/compiler/70.backend/svmg_lowering.spl`): new
  `expr_is_float_valued` predicate — value-based float view over arithmetic ops
  (Add/Sub/Mul/Div/Mod/bitwise/shifts; comparisons excluded, they yield Bool
  words and stay pinned to the mixed diagnostic by
  "rejects a float comparison result compared with a float").
  `lower_expect_to_equal` routes both-float-valued operand mismatches through
  `lower_expr(actual)`, which fails with the precise "unsupported binary
  operator on float operands" diagnostic.
- After: **75/75 PASS** on the tracked seed; canary
  `test/02_integration/app/context_log_modes_spec.spl` 4/4.
