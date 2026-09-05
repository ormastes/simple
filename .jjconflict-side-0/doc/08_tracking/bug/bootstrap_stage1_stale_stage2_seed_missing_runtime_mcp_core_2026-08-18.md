# Bootstrap Stage 1 fails: stale stage2 seed lists deleted runtime_mcp_core.c

- **Date:** 2026-08-18
- **Status:** FIXED (stale seed archived; silent-None diagnostic added)
- **Command:** `SIMPLE_CACHE_SCOPE=bootstrap-0818 bin/simple build bootstrap`
- **Symptom:** Stage 1 fails after a few minutes with
  `Link failed. Objects kept at: .simple/native-objects-*` then
  `Build failed: native-build could not build the core-C runtime archive in .../core_c_runtime`.

## Root cause

Chain of three facts, each verified:

1. **Seed selection prefers stale staged binaries.**
   `src/compiler_rust/driver/src/cli/commands/misc_commands.rs:655-663`
   (`resolve_preferred_simple_binary`) prefers `build/bootstrap/stage3`,
   `full`, then `build/bootstrap/stage2/<triple>/simple` over
   `bin/release/<triple>/simple`. A leftover stage2 from a previous run
   (built 2026-08-18 00:09, 131 MB) was picked as the Stage 1 compiler.
2. **That stage2 predates C-MIG-0013.** Commit `6c52280166e`
   (2026-08-18 03:45) deleted `src/runtime/runtime_mcp_core.c`. The 00:09
   stage2 still embeds `runtime_mcp_core.c` in its core-C runtime input
   list (`strings` on the binary: 1 hit; the fresh 06:12 seed: 0 hits).
3. **A missing input fails silently.** `runtime_inputs_fingerprint`
   (`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:75`)
   does `std::fs::read(...).ok()?` per input — one missing file returns
   `None` from `build_c_runtime_library` (tools.rs:328) *before any cc
   runs* (the kept objects dir contained no `core_c_runtime/` subdir at
   all, and no compiler stderr appeared even with
   `SIMPLE_NATIVE_BUILD_RUST_TRACE=1`). `config.rs:311` then reports
   "could not build the core-C runtime archive", and `mod.rs:1151` wraps
   the same error as "Link failed" — they are ONE error, not a cascade.

Ruled out: real C error under archive flags — all 15 current core-C
inputs compile cleanly with the exact flag set
(`-Os -ffunction-sections ... -std=gnu11 -DSIMPLE_CORE_C_STANDALONE=1`).
Ruled out: contention — the failure reproduced deterministically on an
idle foreground rerun (log:
scratchpad `stage1_rerun.log`, kept dir `.simple/native-objects-wWmKXX`).

## Fix

- Archived the stale seed (never deleted, per no-reaping rule):
  `build/bootstrap/stage2` → `build/bootstrap/archive/stage2-stale-20260818-0009`.
  With it gone, `resolve_preferred_simple_binary` falls through to the
  fresh `bin/release/x86_64-unknown-linux-gnu/simple` (2026-08-18 06:12).
- `tools.rs` (`runtime_inputs_fingerprint`): a missing/unreadable core-C
  input now prints
  `native-build: core-C runtime input \`X\` unreadable in <root>: <err>`
  instead of silently propagating `None`. `cargo check` clean.

## Residual risk

Any staged `stage2`/`stage3`/`full` binary left behind by an aborted
bootstrap goes stale the moment `src/runtime` inputs are renamed/deleted,
and will be silently preferred on the next `build bootstrap`. A
freshness check (staged binary mtime vs. release seed, or validating the
embedded runtime input list against `src/runtime`) in
`resolve_preferred_simple_binary` would close this class.

## Second failure (same day): seed-as-worker takes the INTERPRETED native-build path — 28.4 GB RSS, killed at 5508s (FIXED)

After archiving the stale staged binaries, `bin/simple build bootstrap` on the
fresh seed (deployed 2026-08-18 06:12) failed differently. Stage 1 spawned:

```
bin/release/x86_64-unknown-linux-gnu/simple run src/app/cli/native_build_worker.spl \
  --source src/app --entry src/app/cli/bootstrap_main.spl --entry-closure --strip \
  --threads 1 --timeout 180 -o bootstrap/stage1/simple --backend=llvm-lib
```

i.e. an INTERPRETED worker; kill_simple_monitor killed it at
**rss=28420MB >= 24000MB after 5508s**, no binary produced
("native-build worker timed out ... The interpreted worker loads the whole
compiler + LLVM import graph before any codegen").

Root cause (two stacked misroutes in the Rust seed driver,
`src/compiler_rust/driver/src/cli/commands/misc_commands.rs`):

1. `resolve_preferred_simple_binary()` (~line 668) picks
   `bin/release/x86_64-unknown-linux-gnu/simple` — which is currently the
   RUST SEED itself (redeployed there 06:12). `is_rust_driver_binary()`
   classifies by PATH only; its `contains("/bin/release/")` clause misses the
   relative candidate `bin/release/...` (no leading slash), so the seed was
   classified as a self-hosted binary and invoked with `--backend=llvm-lib`
   (the pure-Simple command shape).
2. Even correctly classified, the seed's own dispatch
   (`driver/src/main.rs` `dispatch_command`) treats `native-build` as a
   pure-Simple tool and interprets `src/app/cli/native_build_main.spl`, whose
   `run_native_build_worker` spawns the interpreted worker above — the
   pathological path. The seed's in-process `native_project` pipeline is only
   reached via `SIMPLE_NATIVE_BUILD_RUST=1` (or a cross-target build), which
   `compile_stage` never set.

Fix (same file):
- `binary_reports_rust_seed()`: probe the chosen compiler with `--version`
  (env-stripped so `SIMPLE_BOOTSTRAP=1`/`SIMPLE_RUST_SEED_WARNING=0` can't
  suppress the banner) and treat a "bootstrap seed" banner as rust-driver.
  Behavior-neutral when a healthy self-hosted binary exists (no banner).
- `compile_stage`: on the rust-driver branch, set
  `SIMPLE_NATIVE_BUILD_RUST=1` so the seed uses its in-process pipeline
  instead of interpreting the worker wrapper.

Verification (2026-08-18, fixed binary
`/mnt/data/tmp/cargo-seed-rebuild/release/simple`, 59,546,088 bytes 07:39):
stage-1 child is now `bin/release/.../simple native-build --source src/app ...
-o bootstrap/stage1/simple` with NO `--backend=llvm-lib` and NO
`run native_build_worker.spl` child; RSS sampled via ps at t=60s and t=150s:
172 MB / 161 MB (vs 28.4 GB pathological). Probe runs were bounded
(`timeout 200/300`), so full stage completion is pending a full run.
