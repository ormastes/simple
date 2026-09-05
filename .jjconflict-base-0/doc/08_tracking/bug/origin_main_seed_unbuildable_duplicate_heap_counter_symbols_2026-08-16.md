# `origin/main` seed is unbuildable — duplicate `rt_heap_*_bytes` symbols; `check-seed-builds-push.shs` cannot catch it

**Status:** OPEN
**Found:** 2026-08-16, at `f6cadcc36aff61d16d988651ea36a040d2af6aad` (== `origin/main`),
while trying to restore a self-hosted toolchain for an SCV coverage review
**Severity:** blocking — the Rust seed cannot be built from `origin/main`, so the
bootstrap (and therefore every pure-Simple self-hosted binary) cannot be produced
**Component:** `src/runtime/runtime_memtrack.c`, `src/compiler_rust/runtime/src/value/heap.rs`,
`scripts/check/check-seed-builds-push.shs`

## Defect

`cargo build --release --bin simple` in `src/compiler_rust` fails at link:

```
rust-lld: error: duplicate symbol: rt_heap_live_bytes
rust-lld: error: duplicate symbol: rt_heap_peak_bytes
collect2: error: ld returned 1 exit status
error: could not compile `simple-runtime` (lib)
```

Both runtimes define the same two symbols:

| side | location |
|---|---|
| C | `src/runtime/runtime_memtrack.c:251` `int64_t rt_heap_live_bytes(void)` |
| C | `src/runtime/runtime_memtrack.c:255` `int64_t rt_heap_peak_bytes(void)` |
| Rust | `src/compiler_rust/runtime/src/value/heap.rs:328` `pub extern "C" fn rt_heap_live_bytes` |
| Rust | `src/compiler_rust/runtime/src/value/heap.rs:334` `pub extern "C" fn rt_heap_peak_bytes` |

They collide because `libsimple_runtime.so` links the C archive with
`--whole-archive`, so the C definitions are pulled in unconditionally alongside the
Rust ones:

```
"-Wl,--whole-archive" "-lruntime_sffi_c" "-Wl,--no-whole-archive"
```

The Rust definitions are the older pair. The C pair was introduced by
**`ed56ad406bc` "fix(runtime): provide core heap snapshot counters"**
(verified: `git show ed56ad406bc -- src/runtime/runtime_memtrack.c` adds both
`int64_t rt_heap_live_bytes(void) {` and `int64_t rt_heap_peak_bytes(void) {`),
then touched again by `14b6f289f0d` and `da0c73296bf`.

## Why every guard is green on an unbuildable tree

This is the 2026-08-11 incident
(`doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`) recurring
through a hole in its own fix.

`scripts/check/check-seed-builds-push.shs` runs **`cargo check`, deliberately not
`cargo build`** — its own header says so at lines 37 and 43-47, reasoning that `check`
runs the full frontend and only skips codegen+link, so it catches E0432/E0599-class
errors identically. That reasoning is sound for *frontend* errors and wrong for this
one: **a duplicate symbol is a link-time error, and `cargo check` never links.**

Measured at this tip, warm target dir:

| command | result |
|---|---|
| `cargo check --release --bin simple` | **exit 0**, `Finished` in 1m45s |
| `cargo build --release --bin simple` | **fails**, duplicate symbol at link |

So the guard passes on a tree whose seed cannot be built. The other six pre-push
guards are all text-and-tree checks and are blind to it by construction. Note also
that `check-c-runtime-compiles-push.shs` uses `clang -fsyntax-only`, which likewise
does not link — its own documented limit ("`-fsyntax-only` does not link") is the same
blind spot from the other direction.

## Downstream effect (how this was hit)

With no seed, there is no path to a working pure-Simple binary:

- `bin/simple` in the shared worktree is a pre-built Rust seed and self-identifies as
  bootstrap-only.
- `bootstrap/stage{1,2,3}/simple` are **byte-identical** (md5
  `2244f18ce2e694fb7ca395e9916404c3`) and all three **segfault (exit 139)** on a
  two-line hello-world; they expose only `compile`/`native-build`.
- `scripts/setup/setup.shs` refuses to create `bin/simple` without a release binary
  ("run bootstrap first"), and the bootstrap needs the seed — which is what fails here.

Net: any work whose evidence bar is "pure-Simple self-hosted" is blocked at this tip.

## Suggested fix

Decide which side owns the two counters and make the other conditional — the C pair
cannot simply be deleted, because `runtime_memtrack.c` also serves C-only/baremetal
builds where the Rust runtime is not linked. Likely shape: guard the C definitions
behind the same conditional that already distinguishes the baremetal/standalone C
runtime from the Rust-hosted one, mirroring however the other `rt_*` overlaps are
handled.

Not attempted here: `src/runtime/runtime_memtrack.c` has three commits in the last day
(`ed56ad406bc`, `14b6f289f0d`, `da0c73296bf`) and is another session's active lane;
editing it from this session risks clobbering in-flight work.

## Guard upgrade

`check-seed-builds-push.shs` should link, not just check, when the range touches
`src/runtime/**` or `src/compiler_rust/runtime/**`. Options, cheapest first:

1. Keep `cargo check` for the common case, but add `cargo build --release -p simple-runtime`
   (the cdylib is where the collision surfaces) when the runtime dirs are touched.
2. Add a cheap symbol-collision check: intersect the `rt_*` symbols **defined** by the C
   runtime with those defined by the Rust runtime and fail on any overlap. This is a
   static check, needs no linker, and is the natural complement to
   `check-runtime-api-regression-push.shs` — which already extracts exactly these two
   symbol sets and deliberately keeps them separate rather than unioned, so the data is
   already there.
