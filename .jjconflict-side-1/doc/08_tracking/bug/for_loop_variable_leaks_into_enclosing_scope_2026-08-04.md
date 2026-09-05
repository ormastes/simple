# `for` loop variable leaks into the enclosing scope and clobbers an outer `val`

**Status:** FIXED IN SOURCE 2026-08-08 — both engines. The loop variable is now
scoped to the loop and no longer clobbers an outer binding. Guard:
`scripts/check/check-for-loop-variable-scoping.shs`. Red against the stale
deployed `bin/simple` until the next seed redeploy. See "Fix 2026-08-08".
**Found:** 2026-08-04

## Symptom

A `for` loop binding is written directly into the enclosing environment instead
of a fresh loop scope. After the loop ends the binding survives, and if the
enclosing scope already had a binding of the same name, that binding is
**overwritten** — even when it is an immutable `val`.

Minimal repro:

```simple
fn main():
    val x = 100
    for x in [1, 2, 3]:
        pass
    print "after loop x = {x}"
```

- **Actual:** `after loop x = 3`
- **Expected:** `after loop x = 100` (loop variable scoped to the loop; the
  outer `val x` is immutable and must be untouched)

Reproduced on both engines:

- `bin/simple run <file>` (Cranelift JIT) → `after loop x = 3`
- `bin/simple test` (tree-walk interpreter) → the spec assertion below fails
  with `expected 3 to equal 100`

Failing spec (pre-existing, not authored for this bug):
`test/03_system/feature/interpreter/control_flow_spec.spl:82` —
`it "creates new scope for loop variable"`, which asserts `x == 100` after
`for x in [1, 2, 3]`.

Command used:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/03_system/feature/interpreter/control_flow_spec.spl
```

## Root cause

`exec_for` binds the loop pattern straight into the caller's `Env` with no
scope push and no save/restore of a shadowed outer binding:

- `src/compiler_rust/compiler/src/interpreter_control.rs:3249` — `fn exec_for(...)`
  takes `env: &mut Env` and never creates a child scope for the loop body.
- `src/compiler_rust/compiler/src/interpreter_control.rs:3324` — the per-iteration
  bind is `bind_pattern(&for_stmt.pattern, &bind_value, env)`, writing the loop
  variable into that same `env`. There is no matching restore after the loop, so
  the last iteration's value persists and any pre-existing binding of the same
  name is destroyed.

Note `exec_for` also dispatches through several specialised fast paths before
reaching the generic body (`try_exec_enumerated_int_array_for_loop`,
`try_exec_int_array_for_loop`, `try_exec_float_array_for_loop`, and siblings at
`interpreter_control.rs:3257-3288`). Each of those binds into `env` the same
way, so a fix must cover the whole family, not just the generic path — otherwise
the leak persists for whichever element type takes a fast path.

For contrast, the free-variable analyser in
`src/compiler_rust/compiler/src/interpreter/expr/control.rs:468-474` models the
loop correctly: it marks `bound.len()`, binds the pattern, walks the body, then
`bound.truncate(mark)`. The executor does not mirror that discipline.

## Why not fixed now

The defect is in the **Rust bootstrap seed** interpreter/JIT, not in `.spl`
product source. Repo rules direct fixes to pure-Simple source and discourage a
seed rebuild unless essential (`.claude/rules/bootstrap.md`,
`feedback_fix_spl_not_rust`, `feedback_no_bootstrap_unless_essential`), and a
correct fix must change scope handling across `exec_for` plus all six
specialised fast-path loops — a scoping-semantics change wide enough to deserve
its own lane with its own regression matrix. It also risks behaviour changes in
code that has come to rely on the leak (any `for i in ...` whose `i` is read
after the loop), so it needs a repo-wide audit of post-loop reads of a loop
variable before it can land safely.

Landing it in this lane would also require rebuilding and redeploying the seed
while several sessions are live and one is mid-rebase.

## Re-triage 2026-08-08 — STILL REPRODUCES, both seed lanes, unchanged

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` (Rust
bootstrap-seed banner). No pure-Simple self-hosted binary is deployed on this
host, so the self-hosted lane remains untested.

This report's minimal repro, run verbatim:

```simple
fn main():
    val x = 100
    for x in [1, 2, 3]:
        pass
    print "after loop x = {x}"
main()
```

    bin/simple run                              -> after loop x = 3
    SIMPLE_EXECUTION_MODE=interpreter bin/simple run -> after loop x = 3

Expected `after loop x = 100`. Both lanes still leak, and both still overwrite
an immutable outer `val`. No behavioural change since 2026-08-04.

**Confirming, not fixing, and the reason is a repo rule rather than difficulty.**
The root cause this report identifies is in `src/compiler_rust/compiler/src/
interpreter_control.rs` — the Rust seed, which is bootstrap-only per CLAUDE.md,
so a triage lane cannot legitimately patch it. The durable fix belongs in the
pure-Simple lowering lane. That does not make the report stale: the pre-existing
spec `test/03_system/feature/interpreter/control_flow_spec.spl:82`
(`it "creates new scope for loop variable"`) is correct and correctly RED, and
must stay that way.

The blocking concern already recorded above still stands and is the real reason
this is not a quick fix: an unknown amount of tree code reads a loop variable
after its loop, so the audit — not the scope push — is the work.

## Fix 2026-08-08 — landed; the recorded blocker turned out not to exist

### The blocker was measured, and it is not real

This report blocked itself on "an unknown amount of tree code reads a loop
variable after its loop, so the audit — not the scope push — is the work." That
audit was done. Across **26,738 deduplicated `for` loops** in all owned `.spl`
(41,580 files; vendor excluded) there are **16** post-loop reads:

- **8** in one file, `test/01_unit/app/interpreter/perf_spec.spl`, whose example
  names literally say "...preserves accumulator **and final loop value**" — a
  deliberate one-per-fast-path pin of the buggy semantics.
- **1** in `src/app/interpreter/control/control_flow_spec.spl`, which already
  ASSERTS this fix and was failing.
- **6** false positives inside ```` ```simple ```` fences in docstrings.

**Zero** genuine reliance in `src/` production code, `examples/`, or `scripts/`.
A 9th real site (`enum_item`) surfaced during verification that the sweep missed
because it reported only the first hit per loop — worth noting as a limit of
that methodology, not of the conclusion.

### Root causes — THREE executor paths plus the compiled lane

The report named `exec_for` in `interpreter_control.rs` and its eight fast paths.
That was correct but incomplete; fixing only it left the spec red while a
top-level repro passed:

1. **`interpreter_control.rs::exec_for`** — renamed the body to `exec_for_inner`
   and wrapped it, so the save/restore happens once at the choke point ALL eight
   fast paths funnel through, rather than eight times.
2. **`interpreter_call/block_execution.rs`, TWO sites** (`'for_loop_own` and
   `'for_loop`) — the closure/block executor, which is the path an `it` block
   body takes. This is why `control_flow_spec`'s "creates new scope for loop
   variable" stayed red after fix 1 while `bin/simple run` on the same source was
   already correct — a discrepancy that is itself the tell for a second executor.
3. **`hir/lower/stmt_lowering.rs` + `hir/lower/context.rs`** — the compiled lane
   leaked for a different reason: `ctx.add_local` does
   `local_map.insert(name, index)` with no scope stack, so `for x in ...`
   permanently REBOUND an enclosing `x` at lowering time. Added
   `FunctionContext::restore_name_binding`, applied to both the scalar and the
   tuple-destructuring paths (the latter restores every destructured name plus
   the synthesized temp).

`Env`/`CowEnv` has no scope stack, so scoping is expressed as save-then-restore —
the same shape the pre-existing match-arm binding leak fix already uses.
Restoration also runs on the error path, so a caught error cannot leave the loop
variable bound. On the lowering side only the NAME MAPPING is restored: the
`locals` slot stays allocated because its index is already embedded in the
lowered body.

### Evidence, both directions

`scripts/check/check-for-loop-variable-scoping.shs` checks two independently
failing properties, each across an int range, int array, float array, text array
and a TUPLE pattern — so a fix covering only some of the eight fast paths, or a
names-collector that forgot to recurse into tuple patterns, is caught:

1. **Shadowing** — an outer `val` of the same name is intact after the loop.
   This is the data-loss case, and it is asserted on BOTH engines.
2. **Non-leak** — a loop variable with no outer binding is not visible after the
   loop. **Interpreter only**, and deliberately: on the JIT an unresolved name
   does not error, it silently lowers to `0` for ANY name (verified directly:
   `print "{totally_undeclared_name}"` yields `0`, exit 0), so a correctly-scoped
   and a leaked variable are indistinguishable there. Asserting it would be
   asserting that separate lenient-lowering defect. The comment in the guard says
   so and says what to do when that is fixed.

It also asserts the loop still WORKS (iteration count, and the variable visible
INSIDE the body), so a "fix" that skipped the body or restored per-iteration
would fail rather than pass.

    # RED — stale deployed bin/simple:
    FAIL — engine 'interpreter': a for-loop CLOBBERED an outer `val` —
    expected 'int_array=100', got: int_array=3
    # GREEN — freshly built seed:
    PASS — 2 engine setting(s) checked: interpreter,jit

Specs: `test/03_system/feature/interpreter/control_flow_spec.spl` and
`src/app/interpreter/control/control_flow_spec.spl` both **23/24 -> 24/24**
(`dropped=0`); the long-red "creates new scope for loop variable" now passes.
`perf_spec.spl` stays **41/41**: its 9 leak-pinning assertions were removed (not
weakened — they asserted the defect) and replaced with a note pointing here, and
the 8 affected example titles were corrected to drop "and final loop value",
which they no longer claim. Each example's accumulator assertion — the actual
perf subject — is untouched.

No regressions: `mutable_by_default_spec` 24/24,
`implicit_self_field_assignment_hint_spec` 5/5, `context_managers_spec` 7/7
(unchanged from its pre-existing baseline), and the array-remove, implicit-self
and try-operator guards all still PASS.

**Not yet closed:** `bin/release/<triple>/simple` predates this fix, so the guard
is red until the next seed redeploy.
