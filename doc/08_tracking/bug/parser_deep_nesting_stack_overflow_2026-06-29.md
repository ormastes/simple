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
parse_primary_expr`). With no depth bound, deep input recurses without limit
and overflows the stack; downstream recursive AST passes amplify it under
`check`.

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
`check` parser/analyzer is what core-dumps today. The pure-Simple fix takes
effect for the `check`/`build` path only after the self-hosted binary is
rebuilt and deployed (bootstrap). Until then the seed retains the old behavior;
the equivalent guard in the seed analysis pass is out of scope here per the
"fix it in pure-Simple, don't fall back to the seed" project rule.
