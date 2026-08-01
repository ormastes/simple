# Leading-operator line continuation does not parse — breaks a landed frozen contract file

**Date:** 2026-08-01
**Status:** FIXED (self-hosted frontend) — see "Fix" below. One narrower seed
gap remains open and is recorded there.
**Severity:** HIGH — `src/lib/common/ui/gpu_web_capacity_manifest.spl`, a frozen
C0 contract already on `main`, currently fails to parse, so every module that
imports it is unbuildable
**Found by:** webrender_gpu_offload lane (wave-1 CPU reference), while writing
`src/lib/common/ui/draw_ir_v3_execution_route.spl`
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(the live `bin/simple` has no `lint`/`test` subcommand, so it could not be
cross-checked — see the open bootstrap/redeploy issue)

## Symptom

Continuing an expression onto the next line with the operator at the START of
the continuation line fails with a whole-file parse error and no location:

```
src/lib/common/ui/gpu_web_capacity_manifest.spl:1:0: error[PARSE001]: Source did not parse
```

## Minimal reproduction

Fails:

```simple
fn q1(a: text, b: text) -> text:
    return a
        + " reason=" + b
```

Also fails with `val`, with `var`, and with a plain reassignment:

```simple
    val line = a
        + " reason=" + b
```

```simple
    line = line
        + " tail"
```

Parses fine — the operator is TRAILING on the first line:

```simple
fn r2(a: text, b: text) -> text:
    return a +
        " reason=" + b
```

Also fine — no continuation at all:

```simple
    var line = a
    line = line + " reason=" + b
```

So the defect is specifically **leading-operator continuation**, independent of
`return` / `val` / `var` / reassignment. Multi-line call arguments, multi-line
`fn` signatures and multi-line struct literals are unaffected.

## Blast radius

`src/lib/common/ui/gpu_web_capacity_manifest.spl` (frozen C0 contract, landed)
uses the leading form at `gpu_web_capacity_breach_receipt`:

```simple
fn gpu_web_capacity_breach_receipt(breach: GpuWebCapacityBreach) -> text:
    return breach.bound
        + " requested=" + breach.requested.to_text()
```

Verified directly:

```
$ simple.pre-segv-fix-20260731 lint src/lib/common/ui/gpu_web_capacity_manifest.spl
src/lib/common/ui/gpu_web_capacity_manifest.spl:1:0: error[PARSE001]: Source did not parse
Found 1 error(s), 3 warning(s), 0 auto-fix(es) available
```

The file is a **frozen contract** (shared rule 1,
`doc/03_plan/platform/structural_compute/README.md`): it must not be edited
in place, so the fix belongs in the parser, not in the contract file. Until it
lands, the capacity manifest cannot be imported by any consumer, and
`test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl` cannot run.

`src/lib/common/ui/draw_ir_v3_execution_route.spl` therefore does NOT import
the capacity manifest; it constructs its capacity-overflow denial from a
command count instead, and carries an in-file boundary note pointing here.

## Why this is a real grammar gap, not a style preference

Leading-operator continuation is the form the repo's own landed code already
uses, it is what a formatter naturally produces for long concatenations, and
it is accepted by the seed compiler's own sources elsewhere. Silently
normalising every call site to the trailing form would hide a parser defect —
`.claude/rules` requires filing it instead.

## Next steps

1. Fix continuation handling in the self-hosted lexer/parser so a line
   beginning with a binary operator continues the previous logical line.
2. Add a regression spec covering `return` / `val` / `var` / reassignment for
   at least `+`, `-`, `and`, `or`.
3. Re-run `lint` on `src/lib/common/ui/gpu_web_capacity_manifest.spl` and on
   its spec; both should go clean with no edit to the frozen file.
4. Re-import `GpuWebCapacityVerdict` into
   `src/lib/common/ui/draw_ir_v3_execution_route.spl` and replace
   `draw_ir_v3_route_capacity_denial` with a verdict-taking form, so the
   breached bound name flows into the fallback receipt.

## Family (measured, not assumed)

Measured with the self-hosted frontend's own parse gate
(`parse_module_silent_checked`, the call `lint` uses for PARSE001), one file per
cell. 19 of 26 cells failed before the fix; all 26 pass after.

FAILED before / OK after — leading operator on the continuation line:

| Operator | val | var | reassign | return | `if` cond | `while` cond |
|---|---|---|---|---|---|---|
| `+ - * / %` | FAIL | FAIL | FAIL | FAIL | FAIL | FAIL |
| `and or` | FAIL | — | — | — | — | — |
| `== != < > <= >=` | FAIL | — | — | — | FAIL | FAIL |
| `??` | FAIL | — | — | — | — | — |

Already OK before the fix, and still OK after (parity cells):

- leading `.method()` chain — the pre-existing leading-dot rule
- a leading operator inside a call argument, a struct-literal field, a list
  element or plain parentheses — `paren_depth > 0` already suppresses layout
- the trailing-operator form (`a +` then the next line) — `token_requires_rhs`

So the reported family was a subset: the defect covered every binary operator,
not only `+ - and or`, and `if`/`while` conditions as well as bindings.

## Fix

`src/compiler/10.frontend/core/lexer_struct.spl` +
`src/compiler/10.frontend/core/tokens.spl`.

The lexer had a leading-`.`/`|` continuation rule and a trailing
`token_requires_rhs` rule, but no leading-operator rule. Added
`CoreLexer.leading_op_continues`, called from both places that decide layout —
`scan_token`'s newline branch (suppresses the Newline) and `handle_indentation`
(suppresses the Indent). Both sites must agree or the parser sees a
half-continued line.

Three guards, all load-bearing:

1. `token_can_end_expr(cur_kind)` — the previous token must be able to END an
   expression. This is what stops `if c:` / indented `-1` from folding the
   block body into the header.
2. the continuation line must be indented STRICTLY DEEPER than the current
   logical line. This is what stops the implicit-return `-1` that DEDENTS out
   of a loop body from being folded into the last statement of that body — the
   live shape in `src/runtime/simple_core/core_string.spl`, `core_array.spl`
   and `core_process.spl`. Without this guard those three runtime files
   silently return 0 instead of -1/-2.
3. the line must start with a binary operator that cannot begin a statement.

Regression spec:
`test/01_unit/compiler/parser_leading_operator_continuation_spec.spl`. It
covers the operator family and both negative shapes above, and it fails to
parse without the fix (verified: PARSE_FAILED before, PARSE_OK after).

## Still open: the Rust bootstrap seed rejects leading comparison/equality

The seed accepts leading `+ - * / % and or`, but rejects a leading
`== != < > <= >=` and a leading operator inside an `if`/`while` condition with
`Unexpected token: expected Colon, found Newline`. `023a60a05aa` fixed the
TRAILING form for those same hand-written `parse_comparison` / `parse_equality`
productions in `parser/src/expressions/binary.rs`; the LEADING form was not
part of that change. The self-hosted frontend is now a strict superset, so the
regression spec deliberately does not assert those cells — the seed is what
executes specs today.
