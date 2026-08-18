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
