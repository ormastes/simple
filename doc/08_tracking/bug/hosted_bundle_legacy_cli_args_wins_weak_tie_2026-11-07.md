# Hosted C bundle: runtime.c's legacy argv trio wins the ELF weak tie

Status: fix-implemented (C runtime). P1.
Component: `src/runtime/runtime.c:2756`, `src/runtime/runtime_native.c:7918`

## Symptom

Bootstrap run 13's Stage 2 compiler native-built `app.t32_cli`, and the
binary printed at startup:

```
[simple-runtime][error] rejected invalid array handle before dereference;
probable compiler/FFI ABI mismatch (value_bits=0x0000b66c3e8092d0)
```

The run-13 t32 binary itself was not retained. `app.t32_cli` does not build
from current `release/1.0.0` with that compiler: 8 `app.mcp_t32.*` units fail
with `Failed to declare module statics`, which is the separate row
`export_list_static_visibility_not_lifted_2026-11-06`.

## Minimal reproduction

`build/repro/r3/main.spl` (not committed) declares
`extern fn sys_get_args() -> [text]`, prints `.len()`, and does nothing else.
Compiler: `/home/yoon/dev/simple-bootstrap/build/bootstrap-opus-13/stage2/aarch64-unknown-linux-gnu/simple`
(sha256 `ef163123…ae5a`).

```
simple native-build build/repro/r3/main.spl --backend=cranelift \
  --runtime-path <empty dir> --threads 1 --cache-dir <fresh> --output r3e
./r3e x y
[simple-runtime][error] rejected invalid array handle before dereference; ... (value_bits=0x0000b66c3e8092d0)
direct=0
```

The handle has clear low tag bits. It is a raw `malloc` pointer, not a
registered core-C array.

## Root cause

Both `runtime.c` and `runtime_native.c` define `rt_cli_get_args`,
`rt_cli_arg_count` and `rt_cli_arg_at`, weak on ELF (`SPL_CLI_ARGS_WEAK` and
`SPL_CORE_ARGV_OWNER`). With two weak definitions the linker keeps the first
one it sees. The hosted bundle lists `runtime` before `runtime_native`
(`70.backend/backend/runtime_compiler.spl`, `var sources = [...]`), so the
link order is `host_runtime.o`, then `host_runtime_native.o`.

`runtime.c` is the legacy value runtime (`#define SPL_LEGACY_VALUE_RUNTIME 1`):

- its `rt_cli_get_args` returns an `spl_array_new()` array, which is never
  registered with the core-C heap;
- its `rt_cli_arg_at` returns a `SplValue` struct, where compiled code expects
  a tagged text word.

`sys_get_args` and `rt_get_args` in `runtime_native.c` forward to
`rt_cli_get_args`, so the legacy array reaches `rt_array_len` /
`rt_core_as_array`. That function refuses it and returns 0, and the program
sees an empty argument list. `runtime.c` defines no `rt_array_*` function, so
compiled Simple code can never consume its legacy array.

## Fix

`runtime.c` now omits the trio when `SIMPLE_RUNTIME_MEMORY_OWNER` is defined.
Every full-bundle composer passes that define and always lists
`runtime_native`: `runtime_compiler.spl` (both the `-D` and `/D` branches) and
`prepare-runtime-owner.shs`. (`native_project/tools.rs`, `p3-manual-link-stage3.shs`
and `sysroot.shs` pass it too but never compile `runtime.c`.) The lanes that
link `runtime.c` alone (`80.driver/driver_api_project_build.spl`,
`90.tools/leak_check/external_runner.spl`) do not pass it, so they keep their
legacy copies. `runtime_bundle_duplicate_symbols_baseline.txt` and
`runtime_symbol_lane_divergence_baseline.txt` still list the trio as a
`runtime.c,runtime_native.c` duplicate: their scan is textual and ignores `#if`;
the two copies are now mutually exclusive per composition.

On Windows, runtime_native.c's copies become strong when the define is set.
Before the fix, runtime.c held the one strong definition there. A lone weak
external does not resolve on COFF, so the strong definition has to move. ELF
stays weak for the Rust-capsule reason documented at `rt_set_args`.

## Evidence

- **Exact-defect check:** `src/runtime/test/rt_cli_args_owner_order_selfcheck.c`,
  linked with `runtime.o` before `runtime_native.o` and then reversed.
  - Before the fix: the hosted order printed the rejected-handle line, then
    `FAIL sys_get_args/rt_get_args/rt_cli_get_args: rt_array_len=0 want 3`,
    then SIGSEGV in `rt_string_len(rt_cli_arg_at())`. The reversed order
    passed.
  - After the fix: both orders print `PASS — 5 argv provider checks`.
- **Generalization (nm overlap census, `runtime.o` vs `runtime_native.o`,
  with the define):** weak/weak ties went from 3 to 0. The remaining overlaps
  are 28 T/W (runtime.c wins), 6 W/T (runtime_native wins) and 43 T/T
  (decided by `--allow-multiple-definition` order). Those are a residual
  ownership audit, not this defect.
- **End to end with the unmodified run-13 compiler:** that compiler compiles
  the worktree's `src/runtime/*.c`. After the fix the same command prints
  `direct=3 tail=2 guarded=3` with no rejected line. The link order is
  unchanged (runtime.o is still first).
- **Standalone variant:** the selfcheck also passes in both orders with
  `-DSIMPLE_CORE_C_STANDALONE=1` added (the hosted dynload lane passes it).
- **Windows:** not built. This host has no Windows SDK headers (`winsock2.h`
  is missing for both `x86_64-w64-windows-gnu` and `-msvc`). Only the
  `SPL_CORE_ARGV_OWNER` truth table was checked, by compiling the macro block
  with `-D_WIN32`: `_WIN32+MEMORY_OWNER` gives T, `_WIN32+STANDALONE` gives T,
  `_WIN32` alone gives W, and ELF+MEMORY_OWNER gives W. A real clang-cl / mingw
  link is still pending.

## Related, not fixed here

- `hosted_native_all_rust_argv_overrides_c_array_owner_2026-11-07`: when
  `libsimple_native_all.a` is in the link, the Rust strong argv family
  overrides C's, and arguments are lost silently.
- The first two r1 builds without `--backend=cranelift --runtime-path` crashed
  the compiler itself (rc=139).
- The hosted link line carries `-lsqlite3`, which CLAUDE.md forbids.
