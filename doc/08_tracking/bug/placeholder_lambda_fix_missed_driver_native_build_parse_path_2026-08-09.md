# Blocker 9 recurs: placeholder-lambda fix was wired into only ONE of two parse paths

Date: 2026-08-09
Status: **FIXED at source level — driver-path pass landed with a sabotage-proven
driver-path regression. NOT yet confirmed end-to-end at native-build level: that
requires a full bootstrap-from-scratch (see the measurement-trap section), which
is blocked on the Rust seed (blockers 10/11).**
Area: 10.frontend / desugar / placeholder_lambda / driver native-build

## Summary

The blocker-9 fix (`144fecf4280`, `transform_interpolated_placeholder_args()`)
is present and correctly wired at `origin/main` `63ee79be7ee`, and its
regression spec passes — but Stage 3 self-host **still fails with the identical
diagnosis**. The fix was wired into `core_frontend_parse()` only. The
driver/native-build path — the one Stage 3 actually uses — does not go through
`core_frontend_parse()` at all.

## Evidence

Instrumented full bootstrap from a clean pinned `origin/main` checkout
(`/home/ormastes/dev/simple-s3bisect`, `63ee79be7ee`), Stage 2 GREEN, Stage 3
run to a verdict, exit 1:

```
[collect-all] 0.0 module(s) poisoned, 8 error(s) collected across 565 source(s) in phase 3 (HIR lowering).
[collect-all]   poisoned: src/compiler/70.backend/backend/lean_backend.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/cuda_type_mapper.spl
[ERROR] phase 3 FAILED
error: ... HIR lowering error in .../lean_backend.spl: unresolved name: _        (x2)
error: ... HIR lowering error in .../cuda_type_mapper.spl: unresolved name: _1   (x6)
```

The 8 errors map exactly onto the **interpolated** placeholder sites, and only
those:

| file:line | expression | placeholders |
|---|---|---|
| `lean_backend.spl:136` | `params.map("({_.0} : {_.1})")` | 2 |
| `cuda_type_mapper.spl:159` | `elements.enumerate().map("{self.map_type(_1.1)} _{_1.0}")` | 2 |
| `cuda_type_mapper.spl:177` | `params.enumerate().map("{self.map_type(_1.1)} p{_1.0}")` | 2 |
| `cuda_type_mapper.spl:187` | same as `:177` | 2 |

The **non**-interpolated sites in the same files (`lean_backend.spl:205`
`params.map(_.0)`, `:390` `params.map(_.1)`, `cuda_type_mapper.spl:138`, `:310`)
compile fine. So the first-pass transform in `parse_call_arg()` works; only the
interpolated-argument case leaks — exactly the case `144fecf4280` intended to
fix.

## Minimal reproducer (6 lines, seconds to run)

`/home/ormastes/dev/simple-build-out/repro/ph.spl`:

```
fn main():
    val params: [(text, text)] = [("a", "i64"), ("b", "text")]
    val plain = params.map(_.0).join(" ")
    val interp = params.map("({_.0} : {_.1})").join(" ")
    print(plain)
    print(interp)
```

Built with the Stage-2 admitted binary (`native-build`, the in-process
pure-Simple driver) it fails with 2 x `unresolved name: _`, pinning the defect
to the driver path in a loop that takes seconds instead of a 20-minute
bootstrap.

## Root cause — two parse entrypoints, fix applied to one

```
core_frontend_parse()                       <-- interpreter / core-compiler path
  src/compiler/10.frontend/core/frontend.spl:27-31
    expand_string_interpolations(first_expr)          <-- promotes STRING_LIT -> INTERPOLATED_STRING
    transform_interpolated_placeholder_args(first_expr)   <-- THE FIX (only here)
```

```
parse_full_frontend()                       <-- driver / native-build path (Stage 3)
  src/compiler/10.frontend/frontend.spl:95 -> :69 parse_full_frontend_with_scope
    parse_and_build_module_scoped()
      src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:926-962
        parse_module_body()
        desugar_collections(0, 0)
        flat_ast_to_module(path)            <-- interpolation sub-parse happens HERE instead
```

Confirmed by grep: `expand_string_interpolations(` has exactly **one** non-doc
call site in the whole tree — `core/frontend.spl:27`. The driver path never
calls it. Instead the flat->rich bridge sub-parses interpolation regions in
`_FlatAstBridge/convert_nodes.spl:622 flat_bridge_build_string_interps()` via
`parse_interpolation_fragment(inner)` (`:663`), attaching them as
`Interpolation` parts on an `ExprKind.StringLit` (`:851-861`), which HIR then
lowers at `20.hir/hir_lowering/expressions.spl:669 lower_interpolation_list()`.

The placeholder transform is never applied anywhere along that chain, so the `_`
/ `_1` identifiers minted by `parse_interpolation_fragment` survive into HIR as
`unresolved name: _`.

The driver entrypoint is `80.driver/driver_source_pipeline_parsing.spl:453
parse_source()` -> `parse_full_frontend(...)` (import at `:6`).

## Why the regression spec did not catch this

`test/01_unit/compiler/frontend/placeholder_lambda_interpolated_arg_spec.spl`
exercises the interpreter/core path, which is the path that was fixed. Any
regression test for this defect must drive the **driver/native-build** path
(`parse_full_frontend`), not just `core_frontend_parse`.

## Suggested fix (NOT applied — needs care, see cycle note)

Add the driver-path counterpart of `transform_interpolated_placeholder_args()`:
for each `EXPR_CALL`/`EXPR_METHOD_CALL` argument that is an unprocessed
`EXPR_STRING_LIT` whose interpolation regions contain placeholders, promote just
that literal via the existing in-place helper
`expr_promote_interpolated_string(idx, value, parts)`
(`core/string_interpolation_expand.spl:108`) and then run
`transform_placeholder_lambda()` on it. Leave every other string literal
untouched, so the broad `StringLit`-with-`Interpolation`-parts representation the
driver path relies on is not disturbed. Call it from
`parse_and_build_module_scoped()` right after `parse_module_body()`.

**Module-cycle note:** it must NOT live in `desugar/placeholder_lambda.spl` —
that module is imported by `core/parser` (`parse_call_arg`), while
`core/string_interpolation_expand.spl` imports `core/parser`. Placing the new
pass in `string_interpolation_expand.spl` (which may import
`placeholder_lambda`, since `placeholder_lambda` imports only `core.ast*`) keeps
the graph acyclic.

Regression must assert the **driver** path, e.g. a `native-build` of the 6-line
reproducer above.

## Fix as landed (2026-08-09)

**The module cycle was illusory.** The note above assumed
`core/string_interpolation_expand.spl` -> `core/parser` -> `desugar/placeholder_lambda`
would trap the new pass, but the actual constraint is weaker: `placeholder_lambda`
imports only `core.ast*` accessors, and `core/parser`, `core/parser_expr` and
`core/lexer` import nothing from `_FlatAstBridge`. So `module_assembly.spl` (which
already imports `core.parser`) can import `string_interpolation_expand` directly
with no cycle. Fix shape 1/2 hybrid, three edits:

1. `desugar/placeholder_lambda.spl` — new exported predicate `expr_has_placeholder(eid)`,
   so the driver path can ask "does this subtree contain `_` / `_N`?" without the
   private `_ph_*` detection globals leaking out of the module.
2. `core/string_interpolation_expand.spl` — new pass
   `expand_interpolated_placeholder_call_args(start_expr)`. Walks `EXPR_CALL` /
   `EXPR_METHOD_CALL` args; for an unprocessed `EXPR_STRING_LIT` arg it parses the
   interpolation regions, and **only if some region contains a placeholder** promotes
   that one literal via `expr_promote_interpolated_string(...)`, then delegates to the
   existing `transform_interpolated_placeholder_args()`. Every other string literal is
   left opaque so `flat_bridge_build_string_interps()` keeps handling it as before.
3. `_FlatAstBridge/module_assembly.spl` — calls the new pass in
   `parse_and_build_module_scoped()` immediately after `parse_module_body()`,
   mirroring where `core_frontend_parse()` runs its counterpart.

### Verification

- **Fast reproducer** `/home/ormastes/dev/simple-build-out/repro/ph.spl` under the
  pre-fix Stage-2 binary: `2 error(s) ... unresolved name: _`, phase 3 FAILED.
- **Regression spec** `test/01_unit/compiler/frontend/placeholder_lambda_interpolated_arg_spec.spl`
  gained a second describe block, `"placeholder lambdas on the driver / native-build
  parse path"`, driving `parse_and_build_module_scoped(src, path, false)` directly
  (`streaming_scope: false` leaves the flat arena intact, so the same flat-array
  assertions apply). `Results: 10 total, 10 passed, 0 failed`.
- **Sabotage parity**: commenting out the single new call site in
  `parse_and_build_module_scoped()` turns the run RED at exactly the driver-path
  lambda oracle — `expected 0 to be greater than 0`, `Results: 10 total, 9 passed,
  1 failed`. The pass is therefore load-bearing, not vacuous. (The driver `leaked_*`
  scenarios are green either way by construction: pre-fix the argument is still an
  `EXPR_STRING_LIT`, so an `EXPR_INTERPOLATED_STRING` scan finds nothing. The lambda
  count is the real oracle.)

### Measurement trap: `resume-stage3-from-admitted.sh` CANNOT validate a frontend fix

A resumed Stage-3 run was attempted against a patched tree and returned the
**identical 8 errors**. That result is *vacuous*, not a refutation:

Stage 3 is *the **Stage-2** binary compiling the compiler source*. The compiler
performing the parse is `stage3/<platform>/stage2-admitted/simple`, built at
07:58 from **pre-fix** source; the patch landed in the source tree at 08:29. A
frontend/desugar fix only changes behaviour once it is *inside* the compiler
doing the compiling, i.e. from the **stage1/stage2 rebuild of a full
bootstrap-from-scratch**. Resuming from an admitted Stage-2 snapshot pins the
compiler to pre-fix behaviour by construction, so the 8 errors were guaranteed
regardless of whether the fix is correct.

Corollary, same trap: the fast reproducer `ph.spl` demonstrates the **defect**
(it runs under the pre-fix Stage-2 binary) but can never demonstrate the **fix**.
Any native-build-level proof of this fix requires a full bootstrap-from-scratch,
which needs the Rust seed — blocked upstream by
`rust_seed_build_broken_on_origin_main_2026-08-09.md` (blockers 10/11).

Two smaller fail-open traps hit on the way, worth not repeating:
- `pgrep -f resume-stage3` **matches the watching shell's own command text**, so a
  liveness check written that way reports RUNNING forever and never fires. Key
  monitors on a captured PID (`kill -0 $pid`), not a pattern.
- `resume-stage3-from-admitted.sh` rejects an **absolute** OUTPUT_DIR at line 6
  (`case "$source_output" in /*|*../*) exit 2`) and exits 2 **silently, with no
  message**. A symlink does not help either (line 8 compares `pwd -P`). The dir
  must be copied to a plain relative path inside the repo root.

## Consequence

`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md` remains
**UNVERIFIED**: Stage 3 again fails closed in phase 3 (HIR lowering) with no
SIGILL, no `field access on nil receiver`, and no exit 132 anywhere, so the MIR
lowering region that bug lives in still never executes.
