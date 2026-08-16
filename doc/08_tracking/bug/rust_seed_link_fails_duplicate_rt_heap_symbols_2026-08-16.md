# Rust seed fails to LINK from a clean target dir: duplicate `rt_heap_*` symbols

**Status:** OPEN
**Found:** 2026-08-16
**Severity:** blocker — no Rust-seed binary can be produced from a clean build
**Scope:** `src/compiler_rust/runtime/src/value/heap.rs`, `src/runtime/runtime_memtrack.c`
**Related:** `doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md` (same
class: a structurally clean tree that does not build)

## Symptom

From a clean `CARGO_TARGET_DIR`, at `origin/main`:

```
cargo build --release --bin simple
...
rust-lld: error: duplicate symbol: rt_heap_live_bytes
rust-lld: error: duplicate symbol: rt_heap_peak_bytes
collect2: error: ld returned 1 exit status
error: could not compile `simple-runtime` (lib)
```

`cargo check --release --bin simple` **passes** — the failure is at link time when
`libsimple_runtime.so` is produced, so any check-only gate is blind to it.

## Cause

Both symbols are defined twice in committed source, once per runtime:

| Symbol | Rust definition | C definition |
|---|---|---|
| `rt_heap_live_bytes` | `src/compiler_rust/runtime/src/value/heap.rs:328` (`pub extern "C" fn`) | `src/runtime/runtime_memtrack.c:251` (`int64_t rt_heap_live_bytes(void)`) |
| `rt_heap_peak_bytes` | `src/compiler_rust/runtime/src/value/heap.rs:334` (`pub extern "C" fn`) | `src/runtime/runtime_memtrack.c:255` (`int64_t rt_heap_peak_bytes(void)`) |

The C runtime is linked with `-Wl,--whole-archive -lruntime_sffi_c`, so every C
definition is pulled in unconditionally and collides with the Rust `extern "C"`
export of the same name.

## Why the existing guards did not catch it

`check-runtime-api-regression-push.shs` evaluates the Rust and C symbol sets
**separately and never unions them** — by design, because they are parallel
implementations. That design decision is correct for detecting *removals*, but it
means a name defined in BOTH is invisible to it: neither set shrank.
`check-c-runtime-compiles-push.shs` uses `-fsyntax-only`, which by its own
documented limitation does not link. `check-seed-builds-push.shs` runs
`cargo check`, which as shown above passes. So all three relevant guards are
green on a tree that cannot produce a binary.

## Unblock condition

Pick one owner per symbol. Either `#[cfg]`-gate the Rust `extern "C"` exports out
when the C runtime provides them, or rename the C definitions to
`rt_heap_live_bytes_c` / `rt_heap_peak_bytes_c` and have the C callers
(`runtime.c:1938`, `runtime_legacy_core.c:584`,
`test/rt_string_free_selfcheck.c:22-23,49`) use those.

Then extend a guard to actually link — the cheapest honest gate is adding a
duplicate-symbol check that compares the Rust and C exported-symbol sets for
INTERSECTION, which is exactly the axis the current separate-sets design leaves
uncovered.

## Impact on the user-`Option` lowering fix

The lowering fix in `hir/lower/expr/control.rs` and `hir/lower/stmt_lowering.rs`
(this session) `cargo check`s clean but cannot be run, because no seed binary can
be linked. Its regression fixture and dual-toolchain SSpec are committed and will
execute the moment either this blocker or the self-hosted toolchain is repaired.
No runtime PASS is claimed for that fix.
