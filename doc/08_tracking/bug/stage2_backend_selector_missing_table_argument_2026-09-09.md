# Stage 2 backend selector receives an omitted dynamic-default argument

Status: source repair and focused native ABI evidence complete; canonical
Stage 2 admission remains pending. This investigation did not rebuild Stage 2,
promote a candidate, or build the Chrome library.

## Failure identity

The second fresh Stage 2 resume output is `build/stage2-resume.WBRMDQ`.
Its retained `stage2/aarch64-apple-darwin/simple.rejected` has SHA-256
`b2584b65dbf085249b8bdeb99cedd40b18650c89399cdd99f0adcc9cb4a46a75`.
The canonical positional hello-world probe returned raw status 139 after MIR.

The same exit code did **not** identify the same crash. The prior candidate
failed in `optimizationpipeline_for_backend +180` reading address `0x30`.
This candidate advances past that function and fails in backend selection:

- PC `0x1005210cc`, `select_static_backend_v1 +200`.
- Faulting instruction `ldr x0, [x8, #0x10]`; `x8=0`.
- Stop reason `EXC_BAD_ACCESS (code=1, address=0x10)`.
- Stack: `select_static_backend_v1` -> `CodegenFactory.create` ->
  `create_builtin_backend_compile_adapter` -> `load_backend` ->
  `CompilerDriver.compile_to_native` ->
  `CompilerDriver.compile_with_reverse_reference_owner_v1` ->
  `CompilerDriver.compile` -> `run_native_build_bootstrap` -> `main`.

Evidence lives in `build/native_probe/astra-stage2-sigsegv-two/`:
`lldb-new.log`, `lldb-callers-address.log`, and `lldb-globals.log`.
The `lldb-new.log` SHA-256 is
`52a7644410d22f0cd06b11663da0fbdc26070fa707fae7878649a0e7515a1b6a`.

## Exact call and environment reconstruction

The production probe is defined by
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs` and invoked
with `CANDIDATE_FRONTEND_BOOTSTRAP=0`, backend `llvm`:

```text
<candidate> native-build --backend llvm --runtime-bundle core-c-bootstrap
  --entry-closure --cache-dir <private-probe>/cache-hello-world-positional
  --mode one-binary scripts/check/cert/redeploy_gate/fixtures/hello_world.spl
  --output <private-probe>/hello_world_positional
```

Working directory: `/Users/ormastes/macos-stage4-codex-20260908`.
The scoped environment sets `SIMPLE_BINARY`, `SIMPLE_BIN`,
`SIMPLE_BOOTSTRAP_DRIVER`, and `SIMPLE_FRONTEND_DELEGATE` to the candidate;
`SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_NO_STUB_FALLBACK=1`,
`SIMPLE_EXECUTION_MODE=` (empty), `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`,
`SIMPLE_BOOTSTRAP=0`, `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`, and
`SIMPLE_LIB=/Users/ormastes/macos-stage4-codex-20260908/src`.

LLDB used these explicit environment settings and argument shape with the
retained rejected filename and new private cache/output leaves under the
evidence directory. It inherited the diagnostic session's host environment,
rather than the canonical bootstrap's isolated HOME/TMPDIR. The original host
environment is recorded in the fresh output's
`stage3/aarch64-apple-darwin/stage2-command.transcript`. This is a diagnostic
reproduction, not a replacement admission receipt.

## Proven cause and dependent initialization gap

The selector declares its second parameter as
`table: [StaticBackendEntryV1] = active_static_backend_table_v1()`.
The original factory supplied only `kind.to_text()`.

Disassembly of the rejected candidate shows `BackendKind.to_text` at
`0x1004ba3fc`, followed immediately by the selector call at `0x1004ba400`.
There is no load of the required table into `x1`. The selector treats the
remaining stack address as its array. At the crash `x20` (the alleged table)
is `0x16fdfe1c8`; its alleged length is a heap address, and `rt_index_get`
returns tagged nil `3` for the first element. Dereferencing its plugin field
then faults. This is not a malformed Option descriptor in MIR optimization.

The producer's HIR lowering explicitly limits default filling to directly
named local functions with constant default expressions:
`src/compiler_rust/compiler/src/hir/lower/expr/calls.rs`, and
`module_lowering/module_pass.rs::collect_fn_param_defaults`. Function-call
defaults are left unfilled; imported defaults are not collected. Native call
emission nevertheless permits the under-arity call. General dynamic/imported
default argument lowering and fail-closed arity diagnostics remain an open
compiler defect; this patch does not claim to implement them.

The retained candidate also shows `_k1_static_backend_table_installed_v1=0`.
The full CLI installs the selected composition before backend use, and the
composition's bootstrap wrappers install it. The positional bootstrap route
calls `CompilerDriver` directly and bypassed both initialization paths.

## Repair

1. `src/compiler/70.backend/backend/codegen_factory.spl` now obtains the current
   active table explicitly and supplies it as the second selector argument.
   The selector, table negotiation, and public API remain intact.
2. `src/app/cli/bootstrap_main.spl` now calls
   `install_selected_k1_backend_table_v1()` before constructing the driver in
   the positional native-build route. A rejected composition returns status 1
   with `PLUG-E-K1-POLICY`; no backend or success result is fabricated.

## Verification and limits

- The actual repaired factory compiled to a native ARM64 object. Its
  disassembly calls `active_static_backend_table_v1`, saves the result in
  `x22`, and emits `mov x1, x22` immediately before the selector call.
  Evidence: `factory-object-disassembly.log`, SHA-256
  `255e5eeec3782b44c0e77a7551d0f84821a54713910fb7aa72cd320e1ba5387f`.
- `test/fixture/native_backend_registry/explicit_dynamic_table.spl` compiled
  with the bootstrap producer, LLVM, `core-c-bootstrap`, and
  `SIMPLE_NO_STUB_FALLBACK=1`. The native binary passed six checks: empty table,
  two existing entries, missing entry, replacement table, and removed entry.
  Evidence: `dynamic-table-build.log` and `dynamic-table-run.log`.
- `test/fixture/native_backend_registry/factory_active_table.spl` exercises
  the real factory and registry with selection-only ports that explicitly
  reject compilation. Its build was attempted with two source-root
  configurations; both stopped in the pre-existing
  `mir_opt/mod.spl` dependency on unresolved `Result.err`. It did not link or
  execute, and is not PASS evidence. Logs: `factory-build.log` and
  `factory-build-composed.log`. No further retry was made.
- `git diff --check` passed for the repair and fixtures.

A future single canonical retry is justified by the changed native call
sequence and corrected initialization boundary. Success is still unproven:
the complete factory fixture, bootstrap initialization behavior, hello-world
link/run, both canonical frontend modes, and Stage 2 admission must pass before
the candidate can produce the canonical Chrome library.
