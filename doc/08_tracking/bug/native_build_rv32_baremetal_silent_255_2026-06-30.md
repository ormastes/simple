# rv32 native-build: silent 255 FIXED; remaining bare-metal rv32 runtime gap

**Date:** 2026-06-30
**Area:** compiler / native-build (LLVM backend, `riscv32-unknown-none`)
**Severity:** the silent-failure + routing defects are FIXED; the remaining boot blocker is a
bare-metal-runtime gap (separate, larger).
**Status:** partially resolved — see below.

## Symptom (original)

`bin/simple native-build --backend llvm --target riscv32-unknown-none ...` exited **255 with no
diagnostic and no ELF**, for any entry.

## Root cause + FIX (resolved)

Two coupled defects, both fixed:

1. **Mis-route to a too-slow interpreted worker (silent 255).** `native-build` is in
   `command_is_pure_simple_tool`, so the dispatcher never reached the in-process Rust
   `handle_native_build`; it always ran the `.spl` app, whose worker (`bin/simple run
   native_build_worker.spl`) eagerly loads the whole compiler+LLVM import graph in the
   interpreter. With a large `--source` set (`src/os`+`src/lib`) it exceeds the timeout budget →
   coreutils `timeout` (124) → `process_ops` remaps to `-1` → `exit(-1)` = 255, with the only
   hint a single `[TIMEOUT]` line buried under thousands of warnings.
   - **Fix A (pure Simple, commit a0652371728):** `native_build_main.spl` now prints an explicit,
     non-truncatable line distinguishing the timeout sentinel and naming the cause/knobs.
   - **Fix B (Rust seed, commit 187c62110138):** route `native-build` to `handle_native_build`
     only when an explicit `--target` is passed (host builds stay on the pure-Simple path).
     `handle_native_build` parses `--target`/`--linker-script`, defaults rv32 to LLVM, threads the
     target into codegen, and links via `ld.lld`.

2. **Result:** `native-build --target riscv32-unknown-none` now **compiles riscv objects and
   reaches the linker with real, actionable errors** instead of a silent 255. The rv32 codegen
   path works.

## Remaining blocker (NOT a toolchain bug): incomplete bare-metal rv32 runtime

Building the firmware self-test (`examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl`, an
array-free scalar RAIN reconstruct) for rv32 now links and reports:

```
ld.lld: error: undefined symbol: rt_native_eq      # emitted for ==
ld.lld: error: undefined symbol: rt_native_neq     # emitted for !=
ld.lld: error: undefined symbol: rt_riscv_uart_put # C stub is riscv64-only
ld.lld: error: undefined symbol: main              # entry-symbol/_start wiring
```
The OS entry (`boot.spl`) similarly lacks `rt_value_as_int` / `rt_array_pop`.

**Verified (discriminators, not inference):** the missing `rt_native_eq`/`rt_native_neq` persist
under **`--release`** (so not an unoptimized-build artifact — typed `i64 != i64` still lowers to a
runtime call) AND under **`--runtime-bundle core-c-bootstrap`** (so not a missing-bundle config).
So the freestanding rv32 runtime genuinely does not provide these primitives.

Additional bare-metal-entry detail: a standalone entry needs a **rooted `_start`** (the linker GCs
all code without one; the build's generated `__simple_sandbox_start` wrapper is empty/`size 0` and
is not a bare-metal entry), and `main` is mangled (not the literal symbol `main`).

**Next step (separate, substantial effort):** provide the freestanding rv32 runtime primitives
(`rt_native_eq`/`neq`, `rt_riscv_uart_put` for rv32, `rt_value_as_int`, `rt_array_pop`, …) and a
bare-metal `_start`/entry, then the firmware self-test (and the OS) link into a bootable ELF.

## Deploy status

Fix A is **live** (`native_build_main.spl` is interpreted from source — no rebuild). Fix B is the
Rust routing change: **committed as source and verified via a freshly-built worktree binary, but
NOT yet in the shared `bin/simple`** (the deployed 54 MB binary predates it). Making it live for
`bin/simple` requires a rebuild + deploy of the self-hosted/seed binary — deliberately deferred to
avoid clobbering the shared binary mid parallel-session churn.
