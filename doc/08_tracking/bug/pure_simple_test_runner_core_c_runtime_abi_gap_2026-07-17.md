# Pure-Simple test runner core-C runtime ABI gap

**Status:** Open
**Date:** 2026-07-17
**Owner:** runtime / bootstrap

## Symptom

The admitted Stage 2 compiler can compile and code-generate
`src/app/test_runner_new/main.spl`, but the fail-closed standalone runner does
not link against `core-c-bootstrap`. Rust-hosted bundles are removed for this
entry and must not be used as a workaround.

## Reproduction

Build with the pure-Simple Stage 2 compiler, bootstrap environment variables
unset, `SIMPLE_NO_STUB_FALLBACK=1`, `--backend cranelift`,
`--runtime-bundle core-c-bootstrap`, `--entry-closure`, and no
`--runtime-path` override. The fresh core-C archive still leaves hosted ABI
references unresolved.

Representative missing groups include process/file/fd operations
(`rt_process_exists`, `rt_file_rename`, `rt_fd_write`), collection/text helpers
(`rt_range`, `rt_array_filter`, `rt_string_trim_start`), test execution
(`rt_cli_run_file`), and two Simple closure symbols (`starts_with`,
`run_spl_doctest_mode`). The full retained linker log is
`build/native_probe/test-runner-stage2-core-c-cranelift/build.log`.

## Required fix

1. Port every live runner ABI dependency to the admitted core-C or proven
   ABI-complete pure-Simple runtime; do not re-enable `native_all`.
2. Fix entry-closure ownership for live Simple helpers so they are linked with
   their canonical mangled symbols.
3. Add a runner-specific runtime-symbol inventory gate, then build and execute
   `simple-test` with stub fallback disabled.

## Progress 2026-07-18

- Fixed the CLI preclosure feature-family owner omission: a cache miss now
  falls back to the existing bounded driver resolver, with a
  directory-sensitive cache preventing reuse across source directories.
- Added focused source and behavior regressions for that resolver path.
- Added one shared Unix/core-C provider for `rt_unix_socket_connect`,
  `rt_fd_close`, `rt_fd_read_until`, and `rt_fd_write`, with archive and pipe
  behavior regressions. Its C syntax and exact pipe-behavior probe pass; the
  one-worker focused Rust test compile reached the 300-second host-contention
  cap (exit 124) before test execution.
- A native runner link rerun and fresh runtime evidence remain open.

## Acceptance

- Core-C runner link has zero unresolved symbols.
- `simple-test --help` exits successfully.
- The focused module-global function-pointer regression executes through the
  runner.
- The font/SPipe focused suite executes without hosted fallback.

## Compiler-entry recurrence 2026-07-24

A fresh pure-Simple compiler-only build completed with 675 compiled files and
zero failures:

`/tmp/simple-root-go-20260724/build/compiler-only-c5-cce8-current-main/stage4-compiler-only/simple`

SHA-256:
`be65e69192920ef1e325c8c2ef3aed78b8f0203b8fb37109c66f6daa2ce56c01`.

Using it with stub fallback disabled, the generic
`src/app/cli/compile_entry.spl` closure produced 678 retained objects, then
failed to link against `core-c-bootstrap`. The live closure retains
Rust-hosted-only `rt_cli_handle_compile` and `rt_compile_to_llvm_ir` paths plus
hosted Cranelift/SFFI helpers. Retrying with `rust-hosted` is invalid because
that bundle is intentionally removed. The retained objects and cache are:

- `build/stage4-ufcs/native-objects-00fdBg`
- `build/stage4-ufcs/cache-be65-full-cli`

Relinking those objects with `libsimple_native_all.a` is diagnostic only and
must not be accepted as a supported compiler or RTL-generation lane. The next
bounded fix is a core-safe compile/VHDL entry closure that does not retain the
hosted compatibility dispatcher, followed by one `core-c-bootstrap` link with
`SIMPLE_NO_STUB_FALLBACK=1`.

## Fixed VHDL runner progress 2026-07-24

ELF inspection corrected the earlier section-layout hypothesis: retained
Cranelift objects already contain distinct per-function `.text.subsection`
sections. The live dependency instead came from two generic runtime branches:
`CompilerDriver.compile`/`aot_compile` and
`compile_module_with_backend("vhdl", ...)`.

The isolated VHDL lane now has:

- `compiler_driver_run_vhdl`, a fixed AOT/VHDL frontend-to-MIR runner that
  bypasses generic mode/output dispatch;
- `vhdl_compile_module_text`, which invokes `VhdlBackend` directly and bypasses
  the generic backend selector;
- a core-safe `vhdl_compile_entry.spl` using that fixed runner;
- consistent per-function/per-data section configuration for the Cranelift
  SFFI AOT constructor, covered by a focused Rust test (PASS);
- a real core-C `rt_path_absolute` provider, covered by the focused runtime C
  probe (PASS).

The third capped native-build stopped during discovery on a multiline
conditional in the new runner at `driver.spl:450`; that compact form was
replaced with the supported single-line condition. The corrected entry has not
yet been rebuilt, so the `core-c-bootstrap` link and real RV32 VHDL output remain
open.

## Re-verification 2026-08-17 (app-rest lane) — LIVE (static evidence)

The named symbols genuinely do not exist in the C runtime:
- `rt_process_exists` — zero definitions anywhere under `src/runtime/`
- `rt_range` — likewise (only Rust `.rlib` hits)
- `rt_file_rename` — exists only as `src/runtime/simple_core/core_fs.spl`,
  not as a C definition

So the core-c bootstrap bundle cannot satisfy them and the ABI gap is real.
Not proven: the link failure itself, which needs a Stage-2 build (out of scope
for this lane).
