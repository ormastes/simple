# `for` loop variable leaks into the enclosing scope and clobbers an outer `val`

**Status:** OPEN
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
