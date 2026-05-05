# Simple-Core Pure-Simple Archive Builder Blocker

## Problem Statement

`doc/03_plan/default_native_runtime_shift_phase2_plan.md` requires a
pure-Simple implementation of the narrow `simple-core` host ABI. The current
repeatable gate, `scripts/check-simple-core-runtime-smoke.shs`, materializes
`build/simple-core/libsimple_runtime.a` from C runtime sources. That archive is
ABI-complete enough for hello, standalone TUI, real TUI app smoke, MCP, and
Simple LSP MCP package validation, but it is not a pure-Simple runtime archive.

## Evidence

- Native-project archive output support now exists in the Rust pipeline:
  `NativeBuildConfig.emit_archive` archives compiled Simple objects without
  linking an executable.
- Regression coverage:
  `test_native_project_emit_archive_writes_static_archive` emits
  `libsimple_runtime.a` from a Simple source file and verifies the archive
  symbol table, including runtime-style `rt_*` and `__simple_*` exports.
- ABI conformance coverage now links the same required-ABI behavior probe
  against `core-c-bootstrap` and any discovered ABI-complete `simple-core`
  archive in `test_core_lane_runtime_required_abi_stdout_stderr_and_values`.
- A first Simple-source module tree exists at `src/runtime/simple_core/`.
  `test_simple_core_source_tree_emits_partial_runtime_archive` builds it as a
  `no_mangle` archive and verifies exact lifecycle plus tagged-value
  constructor exports.
- Cranelift/common backend runtime declarations now skip import predeclaration
  when the current module defines a body for the same runtime FFI name, allowing
  `rt_value_int` and related Simple definitions to be emitted.
- `rt_value_float` and `rt_value_bool` runtime FFI metadata now uses the
  `int64_t` ABI signatures declared in `src/runtime/runtime.h`.
- `src/runtime/simple_core/core_memory.spl` implements the memory ABI family by
  exporting `rt_alloc`, `rt_realloc`, `rt_free`, `rt_memcpy`, and `rt_memset`
  from Simple and delegating to libc host primitives. `runtime.h` now exposes
  matching public prototypes, and the partial archive behavior probe validates
  allocation, memset, memcpy, realloc, and free without linking the C runtime
  archive.
- `src/runtime/simple_core/core_process.spl` implements process/time/panic
  wrappers for `rt_exit`, `rt_time_now_unix`, `rt_sleep_ms`, and `rt_panic`.
  The behavior probe validates `rt_time_now_unix` and `rt_sleep_ms(0)`.
- `src/runtime/simple_core/core_stdio.spl` implements the layout-independent
  stdio flush wrappers `rt_stdout_flush` and `rt_stderr_flush` through libc
  `fflush(NULL)`.
- Native codegen lowers `spl_load_i64`, `spl_store_i64`, `spl_load_u8`, and
  `spl_store_u8` directly to native loads/stores for Simple runtime internals.
  `test_simple_runtime_memory_intrinsics_lower_without_helper_symbols` verifies
  those calls do not leak helper symbols into the archive.
- `src/runtime/simple_core/core_array.spl` implements `rt_array_new`,
  `rt_array_len`, `rt_array_get`, `rt_array_set`, `rt_array_push`, and
  `rt_array_pop` against the fixed core array layout. The partial archive
  behavior probe validates the array operations without linking the C runtime
  archive.
- `src/runtime/simple_core/core_string.spl` implements the remaining string,
  generic length/conversion/slice/equality, stdin byte-read, raw stdout/stderr
  write, and print-alias ABI needed by ordinary `print` lowering.
- `scripts/check-simple-core-runtime-smoke.shs` now builds the selectable
  `build/simple-core/libsimple_runtime.a` archive from the Simple source tree
  instead of compiling the C runtime sources into that lane.
- Pure-Simple required-symbol coverage is now 41 of 41 symbols.

## Required Fix

Add a Simple-source runtime archive lane:

1. Create a `simple-core` Simple module tree implementing the `core-required`
   ABI families from `src/compiler_rust/common/src/runtime_symbols.rs`.
2. Build those Simple objects into `build/simple-core/libsimple_runtime.a` with
   the new native archive mode.
3. Define how pure-Simple runtime modules access required host primitives for
   stdout, stdin, file/env/process, allocation, and process startup without
   reintroducing the C runtime archive as the implementation.
4. Keep extending the ABI conformance probes as new required host-primitive
   families move from the C-backed archive into the generated pure-Simple
   archive.
5. Keep `core-c-bootstrap` as the compatibility floor until the pure-Simple
   archive passes hello, standalone TUI, real TUI app, MCP, and Simple LSP MCP
   smoke gates.

## Status

Partially unblocked: Simple native archive output exists and is tested, and a
`simple-core` Simple module tree can export exact lifecycle, tagged-value,
memory, and process/time/panic symbols when built with `no_mangle`. Remaining
blockers are the array, string, length/conversion/slice/equality, and stdio
families needed to avoid using the C runtime archive as the implementation.
