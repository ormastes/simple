# Rust seed fails to LINK: undefined symbol `rt_time_now_seconds` (2026-08-27)

## Symptom
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`
dies in `rust-seed-build` with exit 101:

```
rust-lld: error: undefined symbol: rt_time_now_seconds
  >>> referenced by simple_compiler.9fb06672bb776e18-cgu.0
error: could not compile `simple-driver` (bin "simple") due to 1 previous error
```

Exactly one undefined symbol; everything else links.

## Root cause
`src/compiler_rust/runtime/src/value/sffi/time.rs` declares
`extern "C" fn rt_time_now_seconds() -> i64` and re-exports it
(`runtime/src/value/mod.rs:371`); `interpreter_extern/time.rs:18,40,69` call it
and `interpreter_extern/mod.rs:2047` registers it.

The only C definition is `src/runtime/runtime.c:2651`, and
`src/compiler_rust/runtime/build.rs` deliberately does **not** compile
`runtime.c` (its own comments at :264 and :328 say so — Rust reimplements that
layer and compiling it in would collide).

`runtime_timestamp.c` carries the seed's bootstrap-only historical-ABI shim
(`#ifdef SIMPLE_BOOTSTRAP_TIMESTAMP_COMPAT`, defined by build.rs) and already
provides the f64 sibling `rt_time_now_seconds_f64`. The i64 variant was never
carried into that block, so the seed had no provider at all.

## Why no guard caught it
`scripts/check/check-seed-builds-push.shs` runs `cargo check --release`, which
runs the frontend and **skips codegen and linking** — a documented limit. An
undefined extern is invisible to it by construction.
`scripts/check/check-c-runtime-compiles-push.shs` uses `-fsyntax-only`, which
also never links, and states that same limit.
`scripts/check/check-no-unresolved-runtime-symbols.shs` is the guard for exactly
this class and is ADVISORY / honestly RED (83 codegen-emitted names undefined),
so it does not block.

Not merge damage: every file on the path is byte-identical to `origin/main`
(`git diff --stat origin/main -- src/compiler_rust src/runtime` shows only the
deleted `target_wt/` build outputs). `origin/main`'s seed does not link either.

## Fix
Add the definition to the bootstrap-only compat block in
`src/runtime/runtime_timestamp.c`, matching `runtime.c`'s implementation:

```c
int64_t rt_time_now_seconds(void) { return (int64_t)time(NULL); }
```

No duplicate-definition risk: the native product build compiles `runtime.c` but
does not define `SIMPLE_BOOTSTRAP_TIMESTAMP_COMPAT`; the seed defines the macro
but does not compile `runtime.c`. `<time.h>` is already included.

Rejected alternative: adding `runtime.c` to the crate's `c_sources` — that is
the symbol-collision path build.rs exists to avoid.

## Status
Fix rides `release/2026-08-27`. Verification is the stage2 build itself
(a successful link is the check that fails if the fix is wrong), plus
`sh scripts/check/check-no-unresolved-runtime-symbols.shs` for the defect-class
neighbours.
