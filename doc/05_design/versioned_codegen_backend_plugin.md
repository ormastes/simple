# Versioned codegen backend plugin detail design

<!-- codex-design -->

## Data model

`BackendRole` has `InterpreterJit` and `CompilerAot`. `BackendCapability`
includes JIT execute, object emit, debug info, optimization, cross-target, and
incremental compilation. `BackendPluginError` distinguishes not found, load,
symbol, ABI, MIR digest, capability, target, provider, and teardown failures.

All cross-library strings and buffers use pointer-plus-length borrowed inputs or
provider-owned result buffers paired with an explicit release operation. No
exception/panic, Simple object, Rust object, collection, or allocator ownership
crosses the boundary.

## Startup flow

1. Driver creates `BackendPluginRequestV1` from role and parameters.
2. Registry resolves a built-in descriptor or canonical dynamic-library path.
3. Loader obtains `simple_backend_plugin_v1` through checked dynamic loading.
4. Admission validates structure size, ABI, provider version, MIR digest,
   requested role, target, and capabilities.
5. Vtable `open_session` returns an opaque handle.
6. `BackendSession` owns handle, library lease, diagnostics, and receipt facts.
7. All MIR compile/finalize/execute calls route through the session.
8. Close releases provider objects before the library lease.

## Defaults and parameters

- Interpreter/JIT: `cranelift`; `--backend=llvm` selects LLVM.
- Compiler/AOT: `llvm`; `--backend=cranelift` selects Cranelift.
- `--backend-plugin=PATH` selects a dynamic provider implementation.
- Environment projection is allowed only at the driver owner and is copied into
  the immutable request; provider code does not read environment variables.

## Diagnostics and observability

Test/debug diagnostics record resolution, load, admission, session-open, first
compile, finalize/execute, and close durations; provider name/version/build ID;
and rejection reason. Normal output remains quiet.

## Compatibility

Existing `CodegenFactory` creation is wrapped first. LLVM and Cranelift adapters
translate the common request/session operations into current APIs. Direct
provider calls are removed only after equivalence tests pass.

## Error rules

No implicit backend substitution. No partially emitted output survives an
admission or compile failure. Teardown runs once, and a teardown diagnostic does
not replace the primary compile error.

## C ABI v1 wire and ownership contract

The complete request packet uses `SBQ1` magic, schema1 and ABI1, followed by
role/capabilities and six length-prefixed fields: backend name, target, CPU,
features, optimization and MIR ABI digest. Features use a u32 item count and
u32 length per UTF-8 item, preserving order and embedded delimiters. The packet
header is48bytes; total size is at most64KiB. Text/item lengths are at most4KiB,
feature count128 and feature section32KiB. Only CPU may be empty to explicitly
request the provider default. Required text is nonempty, strict UTF-8 and NUL-free.
Unknown schema/ABI/role/capability bits, truncation and trailing bytes are rejected
before provider loading. The incomplete historical16byte packet is unsupported.
Plugin path remains a local selection field, separate from provider configuration.

Pure-Simple transport owns encoding and roundtrip validation. Runtime ABI glue
decodes bounded borrowed slices without heap allocation; providers must copy
configuration they retain after open_session returns. Single/batch release and
borrowed-library lifetime are unchanged. This does not implement production
provider descriptors, full MIR fidelity or dynamic loader completion.

`simple_backend_plugin_v1()` returns a borrowed immutable descriptor. Every
structure begins with `abi_version` and `struct_size`, validated before its tail
is read. Text and MIR inputs are borrowed byte slices valid only during a call.
Compile, finalize, and diagnostics outputs are provider-owned
`(data,size,owner_token)` buffers released exactly once through the same
vtable. Consumers release buffers, close the session once, then unload the
library. Native lifecycle, Simple canonical-MIR transport, CLI propagation,
and cache path/content identity are implemented. Interpreter dispatch and the
dynamic session adapter remain open; Phase 3 convergence is unproven.

## `SBH1` AOT handle parity, request parity, and feature attestation (2026-11-18)

Detail design additions for `W3`/`W4` (`C3`/`C4` in `doc/03_plan/compiler/phase3_first_dynlib_architecture_bootstrap_2026-11-18.md`):

1. **V1 baseline retention:** First-provider qualification uses `simple_backend_plugin_v1` with the 48-byte `SBQ1` request header and feature-free baseline target selection. Compiler host ABI (executable format/CRT of the loaded plugin) and emitted target (`request.target`, `request.cpu`, `request.features`) remain distinct fields in receipts and cache keys.
2. **`SBH1` AOT admitted-handle transport (`dynamic_adapter.spl`):**
   - `DynamicBackendAdapter.compile_aot_into_path` acquires an active call pin via `self.lease.begin_admitted_call()`, invokes `backend_plugin_run_admitted_module_v1(provider_handle, self.request, module)` (`SBH1` admitted-handle packet consumed by `spl_backend_plugin_run_v1` in `src/runtime/runtime_backend_plugin.c`), and releases the pin in `self.lease.end_admitted_call()`.
   - Legacy path-based `backend_plugin_run_module_v1(self.provider_path, ...)` is no longer used on admitted AOT sessions, preventing post-admission path reopen drift and guaranteeing that closed/revoked leases fail closed before foreign dispatch.
3. **AOT request parity validator (`target_context_v2.spl`, `dynamic_adapter.spl`):**
   - `backend_plugin_aot_request_parity_diagnostic_v2(request, is_release, opt_level, target_cpu, storage_bindings_count)` compares AOT caller overrides against `self.request`:
     - `is_release` vs `request.optimization` (`debug`/`o0` vs release optimization),
     - explicit `opt_level` vs normalized `request.optimization`,
     - nonempty `target_cpu` vs normalized `request.cpu`,
     - `storage_bindings_count == 0` when V1 wire cannot transport custom storage bindings.
   - Any mismatch returns a structured `PLUG-E-CONFIG-MISMATCH` diagnostic in both `DynamicBackendAdapter` and `BuiltinBackendCompileAdapter` (`compile_aot_module` / `compile_aot_into_path`) instead of silently ignoring caller arguments.
4. **Feature attestation state machine (`model.spl`, `loader.spl`, `session_authority_v2.spl`, `receipt.spl`):**
   - `UnconfirmedV1` (`BackendSessionFeatureAcceptanceV2.Unknown`): assigned to synthetic bridge descriptors in `load_dynamic_backend_v1` when provider capability attestation is absent. Empty `request.features` is admitted with `feature_acceptance: unknown`; nonempty `request.features` fails closed.
   - `ConfirmedEmpty` (`ConfirmedBaseline`): assigned when an admitted descriptor explicitly attests baseline target/CPU with `accepted_features = []`; nonempty `request.features` fails closed with attested provider details.
   - `AcceptedExact` (`ConfirmedFeatures`): assigned only when provider-attested metadata confirms target, CPU, and every requested feature item. `session_authority_v2.spl` and `receipt.spl` hash `(feature_acceptance, accepted_features)` into `_backend_session_result_envelope_sha256_v2` so object/cache artifacts stay isolated per accepted ISA variant.

Unit verification: `test/01_unit/compiler/backend_plugin/dynamic_aot_admitted_parity_spec.spl`, `session_authority_v2_spec.spl`, `target_context_v2_spec.spl`, and `loader_session_spec.spl` (`in-progress / unit-verified`; native `G-DYN-ONE` / `G-CONFIG` provider execution pending).
