# `bin/simple game` runtime dispatch needs bootstrap rebuild

**Priority:** low (script-level invocation works)
**Filed:** 2026-04-25
**Component:** `bin/simple` runtime / dispatch table
**Discovered by:** game2d-framework SStack Phase 7 verification

## Description

After adding `CommandEntry { name: "game", app_path: "src/app/game/main.spl", ... }`
to `src/app/cli/dispatch/table.spl`, the *script* path
`bin/simple src/app/game/main.spl ...` works, but the dispatched form
`bin/simple game new|run|test|inspect` requires the bootstrap binary to be
rebuilt so the new `CommandEntry` is baked into the cached `bin/simple` SMF.

This is the standard bootstrap-rebuild pattern documented in memory
`feedback_extern_bootstrap_rebuild.md` and `feedback_mcp_cache_off_by_default.md`.
The cached compiled wrapper does not pick up source-table edits until the
self-hosted compiler re-emits.

## Repro

After Phase 5 implement landed:

```
bin/simple game new hello       # dispatcher does not recognize 'game'
bin/simple src/app/game/main.spl new hello   # works (script path)
```

## Evidence

- `src/app/cli/dispatch/table.spl` — new `game` row added (Phase 5).
- State file `.sstack/game2d-framework/state.md`:
  - `### 7-verify-rerun-2 W4` item 1: "Bootstrap rebuild for `bin/simple game`
    runtime dispatch (rt_cli_run_file cfg-gated; pre-existing in
    worktree-snapshot WIP commit)".
- `src/app/game/{main,new,run,test,inspect}.spl` — five files exist on disk.

## Suggested fix direction

Run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (per memory
`feedback_extern_bootstrap_rebuild.md`) — *not* `bin/simple build bootstrap`,
which falls through the wrapper whitelist and silently no-ops. Verify
post-rebuild that `bin/simple game new --help` exits 0 with usage text from
`src/app/game/main.spl`.

## Related

- `doc/08_tracking/bug/game2d_render_002_gpu_pipeline_arms.md`
- `.sstack/game2d-framework/state.md` `### 5-implement` Wave-D CLI section

## Deferred 2026-04-25

**Status:** STILL AMBER — bootstrap rebuild attempted and aborted.

`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` failed at the
`rust-seed-build` step with `rust-lld: error: undefined symbol: rt_cli_run_file`
referenced from `simple_runtime::value::cli_ffi::rt_cli_run_file`. The recent
upstream commit `1433559d1d fix(rust-seed): forward rt_cli_run_file to
native_all under driver-hooks` was intended to address this, but a clean
rebuild from scratch on x86_64-unknown-linux-gnu still cannot link the symbol
into `simple-driver`.

**Log:** `build/bootstrap/logs/x86_64-unknown-linux-gnu/rust-seed-build.log`

Per the post-ship sprint hard rule "If bootstrap fails, STOP and report — do
not commit anything", the rebuild was rolled back and no source diff was
created for this ticket. The ticket remains amber and should be re-attempted
after the `rt_cli_run_file` link issue is resolved (likely a missing
`#[no_mangle]` export wiring in `simple-native-all` or a `cfg` gate in
`simple-runtime` that excludes the symbol under the bootstrap profile).

Workaround for users: `bin/simple src/app/game/main.spl new <name>` works
today via the script path.

## Deeper Diagnosis 2026-04-25 (sprint #2)

The prior `1433559d1d` commit was directionally close but addresses the
**compile-error layer** only, not the link-time failure. Root cause is
**Cargo feature unification** across the bootstrap build command:

```
cargo build --profile bootstrap -p simple-driver -p simple-native-all
```

When both packages are built in a single Cargo invocation, features unify
across the workspace:

- `simple-native-all`'s `Cargo.toml` declares
  `simple-runtime = { ..., features = ["driver-hooks"] }`.
- `simple-driver`'s `Cargo.toml` declares
  `simple-runtime = { path = "../runtime" }` (no `driver-hooks`).
- Cargo unifies → `simple-runtime` is built **once with `driver-hooks` ON**
  for both consumers.

In `src/compiler_rust/runtime/src/value/cli_ffi.rs`, the `rt_cli_run_file`
implementation is gated:
- `#[cfg(not(feature = "driver-hooks"))]` → `not_implemented` stub with
  `#[no_mangle]` (would emit the `rt_cli_run_file` C symbol).
- `#[cfg(feature = "driver-hooks")]` → wrapper that forwards to
  `extern "C" { #[link_name = "rt_cli_run_file"] fn rt_cli_run_file_extern(..) }`
  and exposes itself as a Rust-callable `pub extern "C" fn rt_cli_run_file`
  WITHOUT `#[no_mangle]` (relies on someone else providing the C symbol).

When unified to `driver-hooks=ON`, the `simple-driver` binary contains the
**wrapper-only** code; the C symbol `rt_cli_run_file` must come from
`simple-native-all` (which provides `#[no_mangle] pub extern "C" fn
rt_cli_run_file`). But `simple-driver` does **not depend on**
`simple-native-all` — and it cannot, because `simple-native-all` already
depends on `simple-driver` (cyclic dependency).

`-p simple-native-all` builds the staticlib but **does not link it into
`simple-driver`'s `simple` binary**. The binary is therefore left with the
wrapper's `extern { #[link_name = "rt_cli_run_file"] }` declaration and no
provider — hence `rust-lld: undefined symbol: rt_cli_run_file`.

### Fix options (all non-trivial — DEFERRED)

1. **Restructure crate ownership**: move the `simple` bin out of
   `simple-driver` into a new top-level crate that depends on both
   `simple-driver` AND `simple-native-all`, breaking the cycle. ≥ 3 Cargo.tomls
   + `main.rs` migration + workspace surgery.

2. **Build-script link injection**: have `simple-driver`'s `build.rs` emit
   `cargo:rustc-link-lib=static=simple_native_all` and
   `cargo:rustc-link-search=...` to splice the staticlib into the `simple`
   binary at link time. Fragile (target-triple specific) and still leaves the
   logical cycle in place.

3. **Feature decoupling**: introduce a separate Cargo feature on
   `simple-runtime` such that the wrapper-only path is gated independently of
   what `simple-native-all` opts into. Requires re-auditing the entire
   `cli_ffi.rs` cfg layout AND every other place where `driver-hooks` is used.

All three blow the per-ticket 5-file STOP guard. Sprint #2 leaves this amber
with the corrected root-cause documented above. The "missing `#[no_mangle]`"
guess in the prior amber note is **incorrect** — `simple-native-all` already
exports the symbol; the wiring problem is at the link/dependency level.

**Status: STILL AMBER (sprint #2).** No source change committed for this
ticket in sprint #2.
