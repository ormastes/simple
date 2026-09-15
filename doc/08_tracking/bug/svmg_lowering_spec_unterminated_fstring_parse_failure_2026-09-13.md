# `test/01_unit/compiler/backend/svmg_lowering_spec.spl` fails to parse: "Unterminated f-string"

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
