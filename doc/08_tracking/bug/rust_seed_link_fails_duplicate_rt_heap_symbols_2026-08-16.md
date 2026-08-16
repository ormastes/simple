# Rust seed fails to LINK from a clean target dir: duplicate `rt_heap_*` symbols

**Status:** FIXED 2026-08-16 in `93e0b028ffb` (another session) — independently
reproduced and verified here
**Found:** 2026-08-16
**Severity:** was a blocker — no Rust-seed binary could be produced from a clean build
**Scope:** `src/compiler_rust/runtime/src/value/heap.rs`, `src/runtime/runtime_memtrack.c`
**Related:** `doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`
(same class: a structurally clean tree that does not build)

## Symptom

From a clean `CARGO_TARGET_DIR`:

```
cargo build --release --bin simple
rust-lld: error: duplicate symbol: rt_heap_live_bytes
rust-lld: error: duplicate symbol: rt_heap_peak_bytes
collect2: error: ld returned 1 exit status
error: could not compile `simple-runtime` (lib)
```

`cargo check --release --bin simple` **passes** — the failure is at link time,
producing `libsimple_runtime.so`, so any check-only gate is blind to it.

## Cause

Both symbols are defined twice in committed source, once per runtime:

| Symbol | Rust definition | C definition |
|---|---|---|
| `rt_heap_live_bytes` | `runtime/src/value/heap.rs:328` (`pub extern "C" fn`) | `src/runtime/runtime_memtrack.c` |
| `rt_heap_peak_bytes` | `runtime/src/value/heap.rs:334` (`pub extern "C" fn`) | `src/runtime/runtime_memtrack.c` |

`runtime_sffi_c` is linked `-Wl,--whole-archive` into the Rust cdylib
(`runtime/build.rs:271`), so every C definition is pulled in unconditionally and
collides with the Rust `extern "C"` export of the same name.

## Fix (owned by `93e0b028ffb`, not by this lane)

The C fallbacks are marked `__attribute__((weak))`, so a link that also carries
the Rust runtime resolves to the Rust accounting, while standalone C builds keep
the fallbacks. MSVC has no weak attribute and takes the strong `#else` branch,
which is correct there because Windows does not whole-archive this file into the
Rust cdylib.

This lane independently hit the same blocker and prepared a macro-gated variant
(`SIMPLE_RUNTIME_RUST_HEAP_COUNTERS` defined in `build.rs`, `#ifndef` in the C
file). That variant was **dropped in favour of the landed one** — weak symbols
need no build-system coordination and cover links this lane's build.rs never
sees. Recorded per the anti-clobber rule: origin superseded this work, so the
right move was to take origin's.

## Independent verification performed here

Exit status read directly into a variable, never through a pipe (a `| tail`
pipeline reported a false `exit 0` for this exact build earlier in the session):

```
BEFORE: rust-lld: error: duplicate symbol: rt_heap_live_bytes / rt_heap_peak_bytes
AFTER:  cargo build --release --bin simple  ->  BUILD_RC=0
        Finished `release` profile [optimized] target(s) in 2m 53s
        -rwxrwxr-x 59509368 .../release/simple
```

The resulting binary runs a real program end to end.

## Gate gap — still open, owned by nobody

No guard would catch a recurrence:

- `check-runtime-api-regression-push.shs` compares the Rust and C symbol sets
  **separately and never intersects them** — by design, since they are parallel
  implementations. A name defined in BOTH is therefore invisible: neither set
  shrank.
- `check-c-runtime-compiles-push.shs` is `-fsyntax-only`, which by its own
  documented limitation does not link.
- `check-seed-builds-push.shs` is `cargo check`, which passes on the broken tree.

All three are green on a tree that cannot produce a binary. The cheapest honest
gate is an INTERSECTION check between the two exported-symbol sets — exactly the
axis the separate-sets design leaves uncovered. Not implemented here.
