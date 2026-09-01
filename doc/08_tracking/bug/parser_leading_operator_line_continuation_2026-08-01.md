# Leading-operator line continuation does not parse — breaks a landed frozen contract file

**Date:** 2026-08-01
**Status:** FIXED (self-hosted frontend 2026-08-01; Rust bootstrap seed
2026-08-01). The seed/self-hosted divergence is now CLOSED in source — see
"CLOSED 2026-08-01" below. The only residue is that the DEPLOYED
`bin/simple_seed` binary predates the seed fix and still needs a redeploy.
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

UNWOUND. That workaround is gone: the route module now imports
`GpuWebCapacityVerdict`, `draw_ir_v3_route_capacity_denial` takes the verdict
and carries `first_breach_bound` into the route receipt, and the new
`draw_ir_v3_route_apply_capacity` reads `verdict.accepted` in the module
instead of in each caller. Boundary note 2 in that file records the change
rather than being deleted. The frozen file was not edited.

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
4. DONE. Re-imported `GpuWebCapacityVerdict` into
   `src/lib/common/ui/draw_ir_v3_execution_route.spl` and replaced
   `draw_ir_v3_route_capacity_denial` with a verdict-taking form, so the
   breached bound name flows into the fallback receipt
   (`gpu_fallback reason=capacity_overflow level=L4 commands=4096
   bound=max_draw_commands`). Re-verified at `55115a82411`:
   `parse_module_silent_checked` says PARSE_OK for the frozen manifest, and
   PARSE_FAILED again with only `lexer_struct.spl` + `tokens.spl` reverted to
   `69d3e4db82b^`.

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

## CLOSED 2026-08-01: the Rust bootstrap seed now accepts the same family

**Status: the parser-level seed/self-hosted divergence is CLOSED.** The seed
previously accepted leading `+ - * / % & ^ << >> and or` but rejected leading
`== != < > <= >= is in ??`. `023a60a05aa` had fixed the TRAILING form for the
hand-written `parse_comparison` / `parse_equality` productions; the LEADING
form was never added to them, and `??` (in `expressions/postfix.rs`) had the
same gap.

### Root cause

Three productions in `src/compiler_rust/parser/src/` are hand-written rather
than macro-generated, so none inherited the `parse_binary_*!` macros' "Case 2"
leading-continuation arm:

| Production | File | Why hand-written | Operators |
|---|---|---|---|
| `parse_equality` | `expressions/binary.rs` | special-cases `not in` | `== != is in` |
| `parse_comparison` | `expressions/binary.rs` | special-cases chaining `a < b < c` | `< > <= >=` |
| `DoubleQuestion` arm | `expressions/postfix.rs` | postfix loop, not a binary production | `??` |

### Fix

New `Parser::skip_leading_comparison_continuation` in `expressions/binary.rs`,
called from three sites: the `parse_equality` loop, the `parse_comparison`
pre-probe (it MUST run before the "is there a comparison at all?" early return,
or the continuation is unreachable), and the `parse_comparison` chaining loop.
`expressions/postfix.rs` gained a leading-`??` branch in its existing `Newline`
arm alongside the leading-`.` method-chain rule.

The rule MIRRORS the self-hosted `leading_op_continues` rather than inventing a
new one. It reuses `peek_indented_operator_continuation` (already used by the
`indent_required` variant for `+`/`-`), which enforces guard 2 above — the
continuation must be on a STRICTLY more deeply indented line — and returns
`None` on a `Dedent`, so a shallower line can never continue an expression.
`not in` is deliberately excluded from the leading form: bare `not` is a legal
statement start, so accepting it would violate guard 3.

### Verification

All measurements used `cargo test -p simple-parser` against the TIP crate, NOT
the deployed `bin/simple_seed` — that binary is a 2026-07-25 build and
reproduces already-fixed bugs verbatim, which is how three lanes chased phantom
defects this session.

- Regression gate: `src/compiler_rust/parser/tests/leading_comparison_continuation.rs`.
  RED before the fix (5 of 8 tests failing), GREEN after (8/8). It carries two
  controls that pass in BOTH states: a same-indent `< b` that must NOT be glued,
  and a set of deliberate syntax errors that must stay rejected.
- Full parser suite: 927 tests across 40 binaries, 0 failures.
- Corpus differential: all 13,807 `.spl` files under `src/` parsed with the
  pre-fix and post-fix parser. **Zero** files changed verdict (13,637 OK both
  ways) — the change is purely additive.

### Correction: the `if`/`elif` indent boundary was ALREADY closed

The companion report
`seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md`
recorded that an `if`/`elif` condition continuation indented strictly deeper
than the block body was rejected (with `if` at col 4 and body at col 8:
cols 5-8 parse, 9-13 do not). **That is stale.** Measured on the tip crate
BEFORE this change, a 27-cell sweep (`if`/`elif` x `==`/`or` x cols 5..13) is
PARSE_OK in every cell — `parse_condition_block` had already fixed it. The
original measurement was taken against the stale deployed seed binary.

Consequence: `scripts/check/check-seed-parse-superset.shs` RULE B was rejecting
legal code and has been deleted. Its two RULE B fixtures are now pinned as
must-NOT-flag negatives so it cannot be reintroduced.

### Guard status

`scripts/check/check-seed-parse-superset.shs` was narrowed, not deleted:

- RULE A (the operator family) is retained ONLY as a stale-binary gate: the
  deployed `bin/simple_seed` predates this fix, so bootstrap-path source must
  not start using the newly-legal forms until the seed binary is redeployed
  (another lane owns that). The scan has a documented removal condition.
- RULE B deleted (see above).
- NEW `assert_seed_fix_present` asserts the three leading-operator branches are
  still present in the seed source and fails loudly if the divergence reopens.
  Proven non-vacuous: reverting `binary.rs`, reverting `postfix.rs`, and
  deleting the regression test each make the guard exit 1.
- Selftest grew 17 -> 19 fixtures (9 must-flag, 10 must-not-flag); the
  fail-on-zero-files check is unchanged. Full scan still PASSes: 11,304
  bootstrap-path files, 0 hits.

### Not fixed here (pre-existing, unrelated)

The seed accepts `val x = a ==` followed by a dedented `return x`, gluing the
`return` in as the RHS of the trailing `==`. Found while building the
deliberate-syntax-error control; it predates this change and is out of scope.
