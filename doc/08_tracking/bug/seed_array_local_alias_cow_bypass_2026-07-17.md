# Seed (Rust interpreter): arrays alias on local-bind despite Arc/COW design

**Status:** Open (root cause NOT pinned down)  **Found:** 2026-07-17 (task #186, lane S42)
**Path:** `bin/simple run` (Rust seed AST interpreter, `src/compiler_rust/driver` /
`src/compiler_rust/compiler/src/interpreter*`) — sibling of #186's native-side fix
(`src/compiler/50.mir/mir_lowering_stmts.spl`, `maybe_copy_array_value`).

```simple
fn main() -> i64:
    var arr = [10, 20, 30]
    var c = arr
    c[0] = 99
    print("ARR0={arr[0]}|C0={c[0]}")
    return 0
# oracle (seed) prints: ARR0=99|C0=99  (want: ARR0=10|C0=99 -- arrays are value types)
```

Also reproduces via a mutating METHOD call instead of index-assign:

```simple
fn main() -> i64:
    var arr = [1, 2, 3]
    var c = arr
    c.push(77)
    print("ARR_LEN={arr.len()}|C_LEN={c.len()}")
# oracle prints: ARR_LEN=4|C_LEN=4  (want: ARR_LEN=3|C_LEN=4)
```

Both probes fail identically on every variant tried (val-bind, struct array
field, array-of-structs, nested arrays) -- the seed has NO working local-bind
array value-semantics today. Native (this repo's default tool) now diverges
correctly from this buggy oracle per the repo's "arrays are value types" rule
(see the #186 fix commit) -- do not try to make native match this oracle.

## Why this doc exists instead of a fix

`Value::Array` is `Arc<Vec<Value>>` specifically so binds are O(1) (Arc clone)
and mutation is COW via `Arc::make_mut` (see `value.rs` doc comment on
`CowEnv`). Reading the mutation code, BOTH repro paths already look
COW-correct:

- Index-assign (`node_exec.rs` `exec_assignment`, `Expr::Index` arm,
  ~line 955): a `case1_unique` fast path checks
  `Arc::strong_count(arc) == 1 && Arc::weak_count(arc) == 0` before mutating
  via `Arc::get_mut`; the fallback (aliased) path clones the `Value` out of
  `env`, then calls `Arc::make_mut(&mut arc)`, which is documented to clone
  the backing `Vec` whenever `strong_count > 1`.
- Mutating-method dispatch (`interpreter_helpers/patterns.rs`, `push`/
  `append`/etc. around line 513-650): same shape, `env.get_mut(obj_name)` ->
  `Arc::make_mut(arc)`.

By hand-tracing reference counts through `var c = arr` (an `Expr::Identifier`
read that goes through `literals.rs`'s `Expr::Identifier` arm ->
`env.get(name).clone()`, an `Arc::clone`, so `arr` and `c` end up as two
`CowEnv` entries whose `Arc<Vec<Value>>` share one allocation, strong_count
2), `Arc::make_mut` on either mutation path SHOULD see strong_count > 1 and
privatize a fresh `Vec` before writing -- leaving `arr`'s original allocation
(and value) untouched. That is NOT what happens empirically: both `arr` and
`c` observe the mutation.

This contradiction was not resolved within this task's time budget. Candidate
explanations not yet checked:
- `bin/simple run`'s top-level `fn main()` body may execute through a
  DIFFERENT interpreter/env path than the `node_exec.rs`/`CowEnv` code read
  above (e.g. a module-globals-backed path, or a separate top-level-script
  executor) -- the two code paths read as correct in isolation, so the
  likely bug is either in an execution path not yet located, or in a subtle
  `CowEnv` overlay/base interaction not apparent from a static read (e.g.
  `get_mut`'s promotion step, or an intermediate `.clone()` that fails to
  actually bump the `Arc` strong count the way `#[derive(Clone)]` is assumed
  to).
- A custom (non-derived) `Clone` impl for `Value` that does something other
  than `Arc::clone` for the `Array` variant would also explain it, but was
  not found in a `value.rs` scan for a manual `impl Clone for Value`.

## Recommended next step

A follow-up lane should add `eprintln!`/`dbg!` instrumentation (or a debug
build with `RUST_LOG`) at `Arc::strong_count(arc)` immediately before the
`case1_unique` check and before `Arc::make_mut`, run the headline repro, and
observe the ACTUAL strong count at each point -- that will falsify or
confirm the "two execution paths" hypothesis directly instead of further
static tracing. `CARGO_TARGET_DIR` for a scratch build:
`build/cargo_<lane>` (never the shared default) per repo bootstrap rules.

## Scope note

Per repo rule ("Fix .spl not Rust" / pure-Simple-first), and since native
(the default tool) is now fixed and verified (native-smoke-matrix
total=17 pass=17 fail=0 codegen_fallback_hits=0), this seed-side gap is
lower priority: `bin/simple run`/oracle-mode is a bootstrap/comparison tool,
not the default tooling path.
