# core_array_cow_spec hits the 900 s timeout: compound assignment to a function local is a no-op in the core interpreter

- **Date:** 2026-11-14
- **Severity:** P3 as filed (spec timeout); the underlying defect is a silent wrong value in the pure-Simple core interpreter
- **Status:** fixed (timeout and wrong value); one unrelated example still red, see "Residuals"
- **Spec:** `test/01_unit/compiler/interpreter/core_array_cow_spec.spl`
- **Regression spec:** `test/01_unit/compiler_core/interpreter/eval/local_compound_assign_fast_slot_spec.spl`

## Symptom

`seed test test/01_unit/compiler/interpreter/core_array_cow_spec.spl` never printed a
verdict and was killed at 900 s (RSS flat at ~234 MB, so a spin, not a leak).

## Root cause

It is not copy-on-write cost. Running each example alone showed 22 of 25 finishing in
5-19 s, one hanging, and two failing. The hang reduces to:

```
fn main() -> i64:
    var index = 0
    while index < 2:
        index += 1
    0
```

and without the loop, `var other = 5; other += 2` leaves `other == 5`.

The resolver (`interpreter/resolve.spl`) gives every non-shadowed function local a
LOAD_FAST slot, and `eval_ident` reads that slot before the scope map. Plain assignment
(`eval_assign_expr`, `eval_stmt_assign`) writes the scope map and the slot. Compound
assignment (`eval_compound_assign_expr`, `eval_stmt_compound_assign`) wrote only the
scope map, so the next read of the local returned the pre-assignment value. Globals have
no slot, which is why `effects += 1` on a module-level variable worked and hid the defect.

Every guest `while i < n: ... i += 1` therefore spun forever. In the spec that is the
"does not invalidate owned struct children during readonly traversal leases" example;
"releases temporary at leases ..." failed (guest returned 1) for the same reason.

History: the 2026-11-07 record `core_interpreter_array_value_cow_2026-11-07.md` lists the
spec's execution as pending, and no earlier green run was found; the commit that
introduced the slot write for plain assignment is hidden behind the
`88aac2ffe28` tree transplant.

## Fix

`src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl`
(`eval_compound_assign_expr`) and `.../interpreter/eval_stmts.spl`
(`eval_stmt_compound_assign`): after `env_assign`, also write the fast-local slot, with
the same lookup order plain assignment uses (`expr_owner_int` of the target, then
`resolve_is_fast_local`).

The parser only produces the expression form (`stmt_expr_stmt(expr_compound_assign(..))`);
`stmt_compound_assign_stmt` has no caller in `src`, so the `eval_stmts.spl` edit is
parity by inspection and is not exercised by any spec.

No snapshot of the stored value is needed: `val_add`/`val_sub`/... always mint a fresh
int, float or text, and `array += array` is rejected (`type error: cannot add array and
array`), so a compound assignment cannot alias an array.

## Evidence (aarch64 DGX Spark, serial, MemoryMax=16G)

Seed built from the merged tree, sha256
`12056a993f99d12dfb6a110e710b8541ac28dd9308f7bfcbf695488d4ba24308`.

| spec | before | after |
|---|---|---|
| `core_array_cow_spec.spl` | timeout, WALL 900.01 s, RSS 234 MB, no verdict | WALL 31.24 s, RSS 578 MB, 25 executed, 24 passed, 1 failed |
| `local_compound_assign_fast_slot_spec.spl` | 2 of 12 passed (wrong values, guarded loops) | 12 of 12 passed, WALL 10.08 s, RSS 509 MB |

Verdict parity: the 28 top-level specs in `test/01_unit/compiler_core/interpreter/` plus
11 specs in `test/01_unit/compiler/interpreter/` that import the core interpreter gave
byte-identical verdict lines before and after (34 OK, the same 5 not OK, no timeouts).
That sweep ran on the first revision of the fix with the seed built at `2018dc03cca`
(sha256 `0b6cd874519879bc24ca48c4b37f742f11c97044d24ee27dd62ca31dbddcf3fb`); the landed
revision differs only by dropping an unreachable error branch.

## Residuals

1. **Still red, different cause:** "isolates real ExprStoreState constructor getter and
   installed nested snapshots". The guest fixture
   `test/fixtures/compiler/core_array_cow/expr_store_state.spl` does
   `use compiler.core.ast_expr.{...}` and the core interpreter's guest module loader
   answers `failed to load module: compiler.core.ast_expr`. A guest containing only
   `use compiler.core.lexer.{lex_init}` fails the same way, so this is resolution of
   `compiler.core.*` from a guest, not something inside `ast_expr`. Not fixed here.
2. **Review note, no reproduction:** `resolve_stmt` recurses into a statement's `body`
   as statement ids although declaration and assignment statements keep expression ids
   there. A stale slot on an identifier whose name is shadowed in its own function could
   then be written by a compound assignment (plain assignment has the same exposure). The
   stricter `resolve_is_fast_local`-only lookup was not taken because it copies five rows
   per call, the allocation pattern removed in
   `core_interp_per_iteration_array_leak_2026-11-14.md`.
3. **Review note, unverified:** the scope chain is not cut at call boundaries, so a
   callee compound-assigning a global that has the same name as a caller's local may
   update the caller's local. Pre-existing and independent of this fix.
