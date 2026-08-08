# Rust seed `cargo build --release` broken: `rt_dict_free_deep_fn` / `rt_free_deep_fn` not found

- **Date:** 2026-08-07
- **Status:** RESOLVED (approach b — reverted the two dangling registrations)
- **Severity:** was a blocker — no incremental or full Rust-seed rebuild could
  succeed from `origin/main` until this landed

## Symptom

`cd src/compiler_rust && cargo build --release` (warm target dir, otherwise
untouched tree at `origin/main`) fails compiling the `simple-compiler` lib
with:

```
error[E0425]: cannot find function `rt_dict_free_deep_fn` in module `sffi_array`
   --> compiler/src/interpreter/../interpreter_extern/mod.rs:557:53
error[E0425]: cannot find function `rt_free_deep_fn` in module `sffi_array`
   --> compiler/src/interpreter/../interpreter_extern/mod.rs:558:48
```

## Root cause

Commit `b28931ee36d` ("feat(runtime): add Rust twin of rt_array_free_deep
and make it reachable from .spl") added three `insert_simple!` registrations
in `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:556-558`:

```rust
insert_simple!("rt_array_free_deep", sffi_array::rt_array_free_deep_fn);
insert_simple!("rt_dict_free_deep", sffi_array::rt_dict_free_deep_fn);
insert_simple!("rt_free_deep", sffi_array::rt_free_deep_fn);
```

but only implemented `rt_array_free_deep_fn` in
`src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs:655`. No
`rt_dict_free_deep_fn` or `rt_free_deep_fn` exists anywhere under
`src/compiler_rust/` (verified by repo-wide grep). The C runtime
(`src/runtime/runtime_native.c:5602` and `:5618`) does implement both
`rt_dict_free_deep` and `rt_free_deep`, sharing a planner with
`rt_array_free_deep` (`runtime_native.c:5440`), but the Rust interpreter's
`rt_array_free_deep_fn` bridges to a separate **Rust-native** reimplementation
(`src/compiler_rust/runtime/src/value/collections.rs:1878`), not the C
function — so the dict/generic counterparts likely need an equivalent
Rust-native implementation, not just a thin C-FFI thunk. That reimplementation
was not written before the commit landed.

## Evidence

```
$ cd src/compiler_rust && cargo build --release
...
   Compiling simple-compiler v1.0.0-beta (.../compiler)
error[E0425]: cannot find function `rt_dict_free_deep_fn` in module `sffi_array`
error[E0425]: cannot find function `rt_free_deep_fn` in module `sffi_array`
error: could not compile `simple-compiler` (lib) due to 2 previous errors
```
Build ran ~03:46:34–03:47:31 UTC on 2026-08-07, warm target dir (`232G` free
before/after, no ENOSPC).

## Impact

Discovered while implementing U1.3 coverage-primitive prerequisites 2 and 3
(`doc/03_plan/ui/testing/u1_3_coverage_primitive_patch_prep_2026-08-07.md`),
which require a Rust-seed rebuild to verify (`driver/src/main.rs` CLI dispatch
table, `compiler/src/pipeline/lowering.rs` MIR coverage threading). Those two
prerequisites' proposed diffs (already fully specified in the patch-prep doc)
could not be built or verified and were left unapplied to the working tree as
a result — landing unverified Rust compiler edits is explicitly against repo
policy (`.claude/rules/bootstrap.md`, `CLAUDE.md`).

This is a **separate** blocker from the known Stage 3 self-host defect
described in `.claude/rules/bootstrap.md`'s "KNOWN BLOCKER (2026-08-06)"
section (`unresolved type: ByteOrder` in `cache_validator.spl`) — this one
fails at the `cargo build --release` step itself, before Stage 3 is ever
reached.

## Suggested fix

Implement `rt_dict_free_deep_fn` and `rt_free_deep_fn` in
`src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs`, mirroring
`rt_array_free_deep_fn`'s shape (deref-pointer, dispatch on `Value::Int` raw
tagged value, refuse with `0` for interpreter-native `Value::Dict`/other
shapes with no runtime heap object behind them) — but this requires an actual
Rust-native `rt_dict_free_deep`/`rt_free_deep` implementation analogous to
`rt_array_free_deep` in `runtime/src/value/collections.rs:1878`, which does
not exist yet either. Alternatively, revert the two incomplete
`insert_simple!` lines (mod.rs:557-558) until the Rust-native implementations
are ready, restoring buildability without removing the working
`rt_array_free_deep` registration.

## Resolution (2026-08-07)

Took approach (b): reverted the two dangling `insert_simple!` lines in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs` —

```rust
insert_simple!("rt_dict_free_deep", sffi_array::rt_dict_free_deep_fn);
insert_simple!("rt_free_deep", sffi_array::rt_free_deep_fn);
```

removed, leaving the working `rt_array_free_deep` registration intact.

**Why (b) over (a):** confirmed by repo-wide grep that no Rust-native
`rt_dict_free_deep` / `rt_free_deep` implementation exists anywhere under
`src/compiler_rust/` (not even a stub) — only the C runtime
(`runtime_native.c:5602`,`:5618`) has them, and per the root-cause analysis
above the Rust interpreter bridge needs a *separate* Rust-native
reimplementation (like `rt_array_free_deep` at
`runtime/src/value/collections.rs:1878`), not a thin C-FFI thunk. Writing that
recursive-free logic from scratch without an existing pattern to mirror is a
correctness/memory-safety risk (a wrong deep-free is a memory-corruption bug),
so per the task's explicit guidance this was NOT attempted. `b28931ee36d`
landed a partial feature (only the array variant was implemented; the dict and
generic registrations were added without their function bodies) — reverting
the dangling half is a legitimate, honest fix.

**What a correct (a) would require:** write real Rust-native
`rt_dict_free_deep` / `rt_free_deep` primitives in
`runtime/src/value/collections.rs` (mirroring `rt_array_free_deep`'s planner
logic, extended to dict entries and the generic runtime-value case), then add
`rt_dict_free_deep_fn` / `rt_free_deep_fn` interpreter bridges in
`sffi_array.rs` mirroring `rt_array_free_deep_fn`, then re-add the two
`insert_simple!` lines, with a test exercising deep-free of a dict/nested
structure and verifying no double-free/leak. Left open as future work if
`rt_array_free_deep` needs dict/generic siblings.

**Verification:** `cargo build --release` in `src/compiler_rust`, incremental
(warm target dir), succeeded in 1m54s:
`Finished \`release\` profile [optimized] target(s) in 1m 54s`. Smoke-tested
`src/compiler_rust/target/release/simple --version` (prints
`Simple Language v1.0.0-beta`) and `simple run` on a trivial `1 + 2` script
(printed `3`, exit 0). No test added — per the task instructions, approach (b)
needs none. `bin/simple` / `bin/release/**` were not touched.
