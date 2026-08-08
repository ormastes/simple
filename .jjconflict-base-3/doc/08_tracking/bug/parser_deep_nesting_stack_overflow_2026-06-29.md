# Parser: deeply nested expressions overflow native stack (core dump)

**Status:** FIXED (pure-Simple parser); seed deploy-gated
**Found:** 2026-06-29 via toolchain noise/robustness sweep
**Area:** compiler / frontend / parser

## Symptom

`bin/simple check <file>` where the file contains a deeply nested expression
(~175+ nested parentheses) aborts with a native stack overflow and dumps core:

```
thread 'simple-main' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

Measured threshold on this host: depth 150 OK, depth 200 core-dumps (exit 255).
`bin/simple run` on the same input survives — `run` skips the recursive
analysis/lint passes that `check` performs over the AST.

## Root cause

Recursive-descent expression parsing: every structurally nested sub-expression
(parens, brackets, slices, call args, dict/array elements) re-enters
`parse_expr`, and each level costs ~14 native frames down the precedence chain
(`parse_pipe → parse_compose → … → parse_unary → parse_postfix →
parse_primary_expr`). With no depth bound, deep input recurses without limit.

NOTE — `run`/`fmt` survive the same input; only `check` core-dumps. The exact
overflowing routine in the deployed binary was **not located** — that `check`
runs additional recursive AST passes (lint/semantic) over the same tree is the
most likely amplifier, but this is an **inference** from "run survives, check
crashes", not a confirmed finding. The parse-time depth guard fixes it
regardless of which recursive pass overflows, by bounding tree depth before any
pass runs.

## Fix

`src/compiler/10.frontend/core/parser_expr.spl` — `parse_expr` now bounds
recursion at `MAX_EXPR_NEST_DEPTH = 128` (well under the measured crash point,
far beyond any real or machine-generated expression) and emits a graceful
`parser_error("expression nesting too deep (max 128 levels)")` instead of
recursing. Single choke-point guard covers all downstream recursive passes.

## Verification (interpreter — runs pure-Simple source directly)

- depth 300 → graceful errors, returns cleanly, no core dump (`PARSED-OK-NO-CRASH`)
- depth 128 → guard fires with the expected message
- depth 120 → parses clean, 0 guard fires (no false positive)

Regression harness: `test/01_unit/compiler/parser/deep_nesting_guard_check.spl`
— standalone (`bin/simple run`) rather than a `*_spec.spl`, because driving the
full parser through the test daemon exceeds its per-spec timeout (see
`simple_test_nested_runner_timeout_2026-06-28.md`).

## Deploy gate

The currently-deployed `bin/simple` is the Rust seed (`compiler_rust`), whose
`check` is what core-dumps today. The pure-Simple fix takes effect for the
`check`/`build` path ONLY after the self-hosted binary is rebuilt and deployed
via a full bootstrap.

**Honest status:** unlike the matcher / enum-dispatch fixes (which are seed-side
and land on a seed rebuild), this fix is pure-Simple and rides the self-hosted
bootstrap path — which memory records as currently failing at stage3. So
**`bin/simple check <175+ nested parens>` still core-dumps today and will
continue to until a working self-hosted bootstrap deploys this change.** The
residual risk is low: the trigger is adversarial input no real or generated
source produces. A mirrored depth guard in the seed parser was deliberately NOT
added, per the "fix it in pure-Simple, don't fall back to the seed" project rule
— if the self-hosted bootstrap stays blocked and this needs to land sooner, the
follow-up is a depth bound in the seed's `parser/src` expression recursion.

## Related sweep findings (other nesting shapes — NOT crashes)

The same noise probe ran `check` on other deeply-nested shapes to see whether
the crash class was broader than expression parens:

- ~400 nested brackets `[[[…1…]]]` → graceful error, no crash.
- ~600 nested `if` blocks and ~300 nested `match` → no stack overflow
  (`stackpanic=0`), but `check` is very slow (>100 s, timed out under the probe
  budget) on that depth. This is pathological-input slowness, not a crash, and
  far below the severity of the paren core-dump; the statement/block parser
  recursion does not overflow. Left unfixed (no real or generated source nests
  blocks/matches that deep); recorded here so it isn't mistaken for unexplored.
