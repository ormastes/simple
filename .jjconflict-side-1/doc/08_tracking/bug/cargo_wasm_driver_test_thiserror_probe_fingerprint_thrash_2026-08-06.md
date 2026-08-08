# `cargo test -p simple-driver --features wasm --test wasi_capability_enforcement` never converges — FIXED

**Status:** FIXED 2026-08-06 in `src/compiler_rust/vendor/thiserror/build/probe.rs`
(file restored — was silently absent, present nowhere in this repo's git
history).

## What was assumed vs. what was real

The task came in framed as "needs a fix using incremental compilation," with a
prior confirmation that `[profile.dev]`/`[profile.test]` do not set
`incremental = false` and `CARGO_INCREMENTAL` is unset (so incremental is
nominally on). That framing was correct as far as it went but not the real
cause. The real cause is a **broken vendored dependency**, not a missing
Cargo.toml knob, and it silently defeats incremental compilation for
**the whole `simple-driver`/`simple-compiler`/`simple-runtime` dependency
chain, for every feature combination, in every target dir** — not just this
one `--features wasm` invocation.

## Root cause

`src/compiler_rust/vendor/thiserror/build.rs:19` declares:

```rust
println!("cargo:rerun-if-changed=build/probe.rs");
```

This is a relative path resolved against the crate root, i.e.
`vendor/thiserror/build/probe.rs`. thiserror's build script needs that file to
exist on disk (it feeds it to a throwaway `rustc --emit=dep-info,metadata`
invocation to probe for the unstable `error_generic_member_access` feature,
then deletes only its own OUT_DIR scratch copy — `build/probe.rs` itself is a
static, checked-in probe *source* file that ships in the published crate, not
something the script generates).

In this repo's `vendor/thiserror` (v2.0.18, unversioned dir name), that file
was **entirely absent** — confirmed via `git log -- .../vendor/thiserror/build/probe.rs`
(no history, never committed) and `.cargo-checksum.json` containing an empty
`"files": {}` map, which means whatever process populated this vendor
directory did not go through a standard, verifying `cargo vendor` (that
normally records a checksum per file and would have failed the crate's own
build the first time `build/probe.rs` didn't exist). A **sibling** vendored
crate in the same repo, `vendor/thiserror-1.0.69/build/probe.rs`, still has
the file intact — same author (dtolnay), same stable probe pattern across
major versions — which is what let us restore the v2.0.18 copy from a
verified in-repo source instead of guessing at content from memory.

Because the watched file is missing, Cargo's fingerprint system treats it as
**always changed** (`FsStatusOutdated(StaleItem(MissingFile(...)))`), so
`thiserror`'s build script (`build-script-build`) is always dirty. That marks
`thiserror` itself dirty, which cascades via `StaleDepFingerprint` through
every crate that depends on it — in this workspace that chain runs
`thiserror` → `simple-common` → `simple-runtime` → `simple-simd`/`simple-type`
→ `simple-compiler` → `simple-driver` (plus `tracing-appender`, which also
depends on thiserror) — a full recompile of essentially the entire in-repo
crate graph, on **every single cargo invocation, regardless of source
changes, regardless of feature flags, regardless of target dir**. This is
distinct from (and additional to) the feature-unification cache-thrashing
mechanism (cause (d) in the original task framing, which is also real and
independently confirmed — see "Also confirmed" below): even a perfectly
feature-stable, single-target-dir, back-to-back identical invocation could
never reach a "Fresh" no-op state because of this bug alone.

Diagnosed with `CARGO_LOG=cargo::core::compiler::fingerprint=info cargo build
...`, which prints the exact dirty reason per unit:

```
stale: missing "/home/.../vendor/thiserror/build/probe.rs"
fingerprint dirty for thiserror v2.0.18/RunCustomBuild/...:
    dirty: FsStatusOutdated(StaleItem(MissingFile(".../vendor/thiserror/build/probe.rs")))
fingerprint dirty for simple-common v0.1.0/.../simple_common:
    dirty: FsStatusOutdated(StaleDepFingerprint { name: "thiserror" })
fingerprint dirty for simple-runtime v0.1.0/.../simple_runtime:
    dirty: FsStatusOutdated(StaleDepFingerprint { name: "simple_simd" })
fingerprint dirty for simple-compiler v1.0.0-beta/.../simple_compiler:
    dirty: FsStatusOutdated(StaleDepFingerprint { name: "simple_runtime" })
fingerprint dirty for simple-driver v1.0.0-beta/.../simple_driver:
    dirty: FsStatusOutdated(StaleDepFingerprint { name: "simple_runtime" })
```

## Fix

Restored `src/compiler_rust/vendor/thiserror/build/probe.rs` with the same,
stable probe-source content thiserror has used across major versions (copied
from the intact `vendor/thiserror-1.0.69/build/probe.rs` sibling in this same
repo — byte-identical pattern, only the crate version differs). This is a
vendored *data* file, not vendored logic — restoring a missing file to match
what `cargo vendor` should have produced is the minimal, correct fix; nothing
in `build.rs` itself needed changing. Functional risk is zero either way: on
this repo's pinned stable toolchain the probe was always going to fail
(`error_generic_member_access` is nightly-only) whether the file is present
or absent, so restoring it changes nothing about what code thiserror
generates — it only gives Cargo's fingerprint a stable, present file to watch
instead of a permanently-missing one.

## Evidence (`--timings`, isolated `CARGO_TARGET_DIR`, memory-gated: only run
when `free -h` showed ≥20Gi available)

To get a clean signal uncontaminated by this heavily-shared repo's concurrent
sessions (32-core box, ~10 other agent sessions building/testing with
differing `--features` combinations at all times — see "Also confirmed"
below), all timings were measured with
`CARGO_TARGET_DIR=target/isolated-wasm-feature`, isolated from the default
118GB, 2770-distinct-fingerprint shared `target/debug`.

| Run | Command | Crates recompiled | Wall time |
|---|---|---|---|
| 1 (cold) | `cargo build -p simple-driver --features wasm --test wasi_capability_enforcement --timings` | full graph (~500+ incl. wasmer) | **2m 49s** |
| 2 (before fix, byte-identical repeat) | `cargo build ...` (no `--timings`) | 13 (driver, common, simd, parser, native_loader, runtime, term-io, dependency-tracker, type, wasm-runtime, compiler, thiserror, tracing-appender) | 28.70s |
| 3 (before fix, byte-identical repeat of run 2 — proves it never converges) | `cargo build ...` | 13 (same set) | 28.53s |
| 4 (after restoring probe.rs, transitional) | `cargo build ...` | 13 (same set — one more forced rebuild to record the corrected fingerprint) | 28.48s |
| 5 (after fix, repeat) | `cargo build ...` | **0** | **1.75s** (Finished in 1.75s / wall 2.53s) |
| 6 | `cargo test -p simple-driver --features wasm --test wasi_capability_enforcement` (test profile, cold) | full test-profile graph | 4m 35s — **test passes, 16/16, in 0.01s. Not a hang.** |
| 7 | same `cargo test` command repeated | **0** | 1.80s build / 2.60s wall total, 16/16 still pass |

Runs 2→3 are the direct proof this was a real, unbounded defect and not
measurement noise: same command, same flags, same target dir, zero source
changes in between (checked via `find ... -newermt` across every relevant
`src/` tree in the narrow window between the two runs — nothing touched), yet
13 crates rebuilt both times. Runs 4→5 are the direct proof of the fix: the
exact same command, one build after restoring the file, finally reaches 0
crates / a true Cargo "Fresh" no-op.

**The earlier agent's "hang" is explained by run 6/1's cold-build cost
compounding with this defect**: every time anyone re-invoked the command
without an isolated target dir, they paid a large fraction of a full
recompile again, indistinguishable from a hang if watched impatiently on a
loaded box. The test itself does not hang or deadlock — 16/16 assertions
pass in 0.01s once the binary exists.

## Also confirmed (real, but not the primary fix target here)

Cause (d) from the original task framing — feature-unification cache
thrashing across concurrent, differently-featured invocations sharing the
default `target/debug` — is independently real and visible on disk right now:
`target/debug/.fingerprint/` holds **2770 distinct fingerprint-hash
directories**, including **87** for `simple-compiler` alone and **~180** for
`simple-driver`, spanning 2026-08-05 through 2026-08-06 (`target/debug` itself
is 118GB). This repo is built continuously by ~10 concurrent agent sessions
with wildly different `--features` selections (`llvm`, `gui`, `pytorch`,
`tui`, `oauth`, `wasm`, `wasm-wasi`, various combinations, `default` alone),
each of which is a legitimately distinct Cargo unit graph and cannot share
compiled artifacts by design — that part is inherent to how Cargo's resolver
v2 keys artifacts by enabled-feature set, not a bug to fix here. **Do not
attempt to "fix" this by disabling feature unification or picking one
canonical feature set for the shared target dir** — that would just move the
thrashing onto whichever other feature combination lost the coin flip. The
practical mitigation, if this specific test needs to be run repeatedly and
reliably fast, is what was used for measurement here: give it (or any other
fixed, narrow feature combination that needs a stable incremental cache) its
own `CARGO_TARGET_DIR`.

Separately, `driver/build.rs` emits
`cargo:rerun-if-changed=<project_root>/test` (the whole `test/` tree, plus one
line per discovered `.spl` file) to regenerate its `.spl`-wrapping Rust test
functions. In this shared repo, `test/` sees constant write activity from
concurrent `bin/simple test ...` sessions, so `simple-driver`'s own build
script legitimately reruns often. This is expected/by-design (it needs
freshness to pick up new/changed `.spl` tests) and, unlike the thiserror bug,
does **not** cascade to `simple-compiler`/`simple-runtime` — `simple-driver`
is a leaf in the dependency graph, so this costs only a cheap relink of
`simple-driver` itself, not a rebuild of its dependencies. Left as-is; not a
defect.

## Files changed

- `src/compiler_rust/vendor/thiserror/build/probe.rs` — restored (was
  missing; content copied verbatim from the intact
  `vendor/thiserror-1.0.69/build/probe.rs` sibling in this repo).
