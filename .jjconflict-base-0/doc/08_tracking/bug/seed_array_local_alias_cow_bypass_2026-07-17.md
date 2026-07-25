# Seed (Rust interpreter): arrays alias on local-bind despite Arc/COW design

**Status:** Fixed 2026-07-19 (lane W9b)  **Found:** 2026-07-17 (task #186, lane S42)
**Path:** default JIT path only -- `bin/simple run` -> `ExecCore::run_file_jit`
(`src/compiler_rust/driver/src/exec_core.rs`) -> `simple_compiler::mir::lower_to_mir`
(`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`, `HirStmt::Let`) --
sibling of #186's native-side fix (`src/compiler/50.mir/mir_lowering_stmts.spl`,
`maybe_copy_array_value`). The tree-walking AST interpreter
(`src/compiler_rust/compiler/src/interpreter*`, reachable via
`SIMPLE_EXECUTION_MODE=interpret`) was already correct and is NOT part of this
bug -- see "Root cause CONFIRMED" below.

## Root cause CONFIRMED (2026-07-19, lane W9b)

The "two execution paths" hypothesis in the original writeup below was
correct, and is now empirically confirmed instead of merely suspected:
`ExecCore`'s default `execution_mode` is `ExecutionMode::Jit`
(`exec_core.rs`, env var `SIMPLE_EXECUTION_MODE`, default when unset), so
`bin/simple run some.spl` dispatches through `run_file_jit` ->
`simple_compiler::mir::lower_to_mir` (a Rust MIR lowering pass, entirely
separate from the pure-Simple compiler's `mir_lowering_stmts.spl`) ->
Cranelift/LLVM JIT, NOT through the `node_exec.rs`/`CowEnv` tree-walking
interpreter this doc originally instrumented. Confirmed by tracing with
`SIMPLE_NATIVE_BUILD_RUST_TRACE=1` (prints `[rust-jit] ...` for the headline
repro) and by forcing `SIMPLE_EXECUTION_MODE=interpret`, which prints the
CORRECT `ARR0=10|C0=99` -- the interpreter's `Arc`/`CowEnv` reasoning in this
doc's "Why this doc exists instead of a fix" section was right all along; it
just wasn't the code path the default CLI actually runs.

The real bug: `lowering_stmt.rs`'s `HirStmt::Let` arm lowered a LOCAL
variable declaration's initializer with `let vreg = self.lower_expr(val)?;`
then stored `vreg` straight to the new local's address with no copy --
exactly the pre-#186 pure-Simple bug, in a separate Rust implementation of
the same lowering pass. `arr` is a heap-allocated, pointer-represented
`RuntimeArray` handle; `var c = arr` therefore aliased the same heap array a
second time.

### Fix

Added `MirLowerer::hir_expr_is_place` (mirrors the pure-Simple compiler's
`mir_expr_kind_is_place`: true for `HirExprKind::Local`/`Global`/
`FieldAccess`/`Index`, i.e. a read of an EXISTING binding, false for a fresh
literal/call-result initializer) and, in the `HirStmt::Let` arm right after
`lower_expr(val)`, a guard `is_array_place_alias` that's true when the
initializer is a place-read AND the declared/value type resolves (via
`TypeRegistry::get_array_element`) to an Array whose element is NOT `u8`.
When true, the vreg is passed through a new `rt_array_copy(vreg)` call
(reusing an existing Rust runtime fn, `runtime/src/value/collections.rs`,
already doing exactly the shallow `rt_array_new`+per-element-`rt_array_push`
copy the pure-Simple #186 fix hand-rolled -- it just wasn't declared for
JIT/AOT call codegen) before the result is stored to the new local. Also
registered `rt_array_copy`'s signature in
`compiler/src/codegen/runtime_sffi.rs`'s shared `RUNTIME_FUNCS` table (used
by both the Cranelift and LLVM backends) so codegen can emit the call.

Files: `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`,
`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`.

### Known residual gaps (out of scope for this fix, same scope boundary as #186)

- **`[u8]` byte-packed arrays still alias.** Byte arrays use a separate
  `rt_byte_array_new`/`rt_typed_bytes_u8_push` heap layout that
  `rt_array_copy`'s `rt_array_push`-based copy loop does not understand
  (verified: `rt_array_copy` assumes 8-byte tagged-word elements). The guard
  explicitly excludes `elem == TypeId::U8`, so `var c = byteArr` for a
  `[u8]`-typed `byteArr` is a known, intentional gap, not an oversight.
- **Plain reassignment (`c = arr` without `var`/`val`, `HirStmt::Assign`)
  still aliases** -- verified empirically (`ARR0=99|C0=99` unchanged). #186's
  native fix and this fix both scope to `HirStmt::Let` (declaration-time
  bind) only; `Assign` was not touched, matching the sibling fix's precedent
  exactly. If `arr = other_array` reassignment aliasing is later found to
  matter, it needs its own follow-up (same `hir_expr_is_place`/
  `rt_array_copy` shape would apply in the `HirStmt::Assign` arm).

### Verification

- Manual repro (`SIMPLE_RUST_SEED_WARNING=0 <built seed> run repro.spl`):
  before fix `ARR0=99|C0=99` (bug), after fix `ARR0=10|C0=99` (correct); the
  `.push()` variant likewise went `ARR_LEN=4|C_LEN=4` -> `ARR_LEN=3|C_LEN=4`.
  Nested-array (`m[0]` place-read) and chained-alias (`e`->`f`->`g`) variants
  also verified correct after the fix.
- Added Rust regression tests in
  `src/compiler_rust/driver/tests/runner_tests.rs`:
  `runner_array_local_alias_is_value_copy` (both interpreter+JIT via
  `run_expect`/`RunningType::Both`) and
  `runner_array_local_alias_is_value_copy_jit_only` (JIT-only via
  `run_on(Backend::Jit, ...)`, pinned so the guard can't be masked by a
  passing interpreter result). Both use an explicit `fn main() -> i64:` body
  with LOCAL `var` bindings + `return` -- a top-level `main = <expr>` script
  form (used by other tests in this file) binds a MODULE GLOBAL rather than a
  local and does NOT reach `HirStmt::Let`/`lower_local_expr` at all; this was
  confirmed the hard way (that source form passed even with the fix
  temporarily disabled) before switching to the `fn main()` form, which does
  reach the buggy path.
  - Fail-first: with the fix temporarily disabled
    (`is_array_place_alias = false && ...`), both new tests FAILED with
    `left: 99, right: 10` (the exact aliasing signature).
  - With the fix restored: `cargo test -p simple-driver --test runner_tests`
    -> `test result: ok. 48 passed; 0 failed`.
  - Regression sweep: `cargo test -p simple-compiler --lib array` (array/mir
    lowering/codegen tests) -> `86 passed; 5 failed`, and the 5 failures were
    verified byte-for-byte IDENTICAL on the unmodified pristine tree
    (`rt_array_clear`/`rt_index_get`/`rt_index_set` "missing runtime fn" in
    `codegen_shared_tests`, plus `test_empty_array_append_refines_indexed_element_type`
    and `test_value_to_runtime_array`) -- pre-existing, unrelated to this fix.

## Original writeup (2026-07-17, root cause not yet pinned down at the time)

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
