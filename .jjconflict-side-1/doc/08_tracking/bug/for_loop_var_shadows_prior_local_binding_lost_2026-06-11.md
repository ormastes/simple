# BUG: `for X in arr` after an earlier `val/var X` in the same fn — loop var binding lost

Status: PARTIALLY FIXED (native/MIR fixed; interpreter still open)

**Date:** 2026-06-11
**Severity:** High (silent wrong values; root cause of stage4 10th-site (b) `check` "1 of 0 file(s)")
**Found by:** stage4 validation matrix follow-up (process_safety plan item 6)

## Problem

When a `for` loop variable reuses a name that was already declared with `val`
or `var` anywhere earlier in the same function (including inside a sibling
`if`/`while` block — block locals leak to function scope), the loop body does
not see the iterated element:

```simple
fn t():
    var bar = "X"          # any earlier val/var with the same name
    for bar in ["p", "q"]:
        print(bar)         # interpreter: prints 0 (Int!), twice
                           # native (pre-fix): nil → interpolations print as
                           # fully blank lines, .len() returns -1
```

A fresh loop-variable name works in both modes.

## Impact found in production code

`src/app/cli/check.spl` `run_check`: `val arg` in the arg-parse `while` loop +
`for arg in file_args:` → in the compiled stage4 CLI the loop ran with
`arg = nil`, `_collect_spl_files(nil)` found nothing, the
`"ERROR: file not found: {arg}"` print rendered as a blank line, and check
reported `✗ 1 error(s) found in 1 of 0 file(s)` for a clean file.

## Root cause (native / MIR) — FIXED 2026-06-11

`hir/lower/context.rs add_local` always appends a new local slot and points
`local_map[name]` at it, so the loop body's `HirExprKind::Local(idx)` refers to
the NEWEST same-named slot. But the `HirStmt::For` / `lower_for_range` binders
in `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` resolved the
loop variable by FIRST name match over params-then-locals, so the element was
stored into the stale earlier slot while the body read nil from the newest.

Fix: both binders now search locals newest-first (and prefer locals over
params, since HIR always materializes the loop var as a local). Regression
test: `mir/lower/tests/basic_lowering.rs
test_for_loop_var_binds_newest_shadowed_local`.

Remaining (pre-existing) edge: a `val X` *inside* the for body that re-shadows
the loop var name still mis-binds (newest-first picks the body local). Rare;
the principled fix is threading the loop-var local index through
`HirStmt::For` instead of a name.

## Root cause (interpreter) — OPEN

The seed AST interpreter (`interpreter_control.rs exec_for` →
`bind_pattern` → `CowEnv::insert`) looks correct in isolation, yet the body
observes `Int(0)` for the loop var whenever ANY same-named binding pre-exists
(`/tmp/v7.spl` repro above: prints `0` per iteration; string interpolation
containing the var renders the whole line empty; `.len()` gives -1).
Mechanism not yet isolated — suspect one of the `try_exec_*_for_loop` fast
paths or const/immutable-name tracking (`CONST_NAMES` / `IMMUTABLE_VARS`)
diverting identifier resolution. Needs a dedicated pass.

## Repro

```bash
cat > /tmp/v7.spl <<'EOF'
fn t_var_decl():
    var bar = "X"
    for bar in ["p", "q"]:
        print(bar)
fn main() -> i64:
    t_var_decl()
    0
EOF
bin/simple /tmp/v7.spl          # prints 0,0 — expected p,q
```

Related: `array_push_loop_in_main_len_coredump_2026-06-11.md` (separate
in-`fn main` array crash family hit while minimizing this repro).
