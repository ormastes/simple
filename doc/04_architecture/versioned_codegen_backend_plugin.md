# Versioned LLVM/Cranelift backend plugin architecture

<!-- codex-architecture -->

## Context

The compiler already owns `Codegen`, `BackendKind`, backend selectors, and
factories under `src/compiler/70.backend/backend/`. LLVM and Cranelift remain
statically coupled at several caller and SFFI sites, and Phase 3 linking can
select a compiler without admitting the matching `rt_cranelift_*` provider.

## Decision

Use an Adapter plus versioned provider ABI. Keep `Codegen` as the internal
pure-Simple semantic contract. Add a concrete plugin boundary that never passes
Simple trait objects or heap graphs across a shared-library ABI.

The shared contracts are:

- `BackendPluginRequestV1`: role, backend name, target, CPU/features,
  optimization policy, MIR ABI digest, and required capabilities.
- `BackendPluginDescriptorV1`: ABI/version/size, provider identity/build ID,
  supported roles/targets/capabilities, and a vtable.
- `BackendPluginVTableV1`: open session, compile module, finalize object,
  execute, retrieve diagnostics, and close session.
- `BackendSession`: admitted descriptor plus opaque provider-owned handle.

Dynamic providers export exactly `simple_backend_plugin_v1`. Built-in LLVM and
Cranelift adapters return the same descriptor and use the same admission path.
The loader uses the canonical checked dynamic-library facade; raw `dlopen` and
`dlsym` remain inside its SFFI owner.

## Selection

`load_backend(request)` is the only startup entry. Interpreter/JIT requests
Cranelift by default; compiler/AOT requests LLVM by default. `--backend` changes
the requested name. `--backend-plugin` optionally supplies a library path.
Explicit or default selection failing admission returns an error and never
silently switches providers.

## Layering

- `00.common`: ABI-safe request, descriptor metadata, errors, receipt schema.
- `70.backend`: loader, admission, session, LLVM and Cranelift adapters.
- `80.driver`: role-aware default policy and CLI parameter projection only.
- `95.interp`: requests an admitted session; no provider-specific calls.
- foreign provider libraries: implement only the versioned ABI.

## Cache and invalidation

Backend sessions are command-scoped. Descriptor metadata is cached by canonical
library identity plus file identity. Any library identity, build ID, ABI/MIR
digest, target, CPU feature, role, or optimization change invalidates compiled
artifact reuse.

## Consequences

One interface supports static and dynamic operation and prevents Phase 3 symbol
authority drift. The ABI requires explicit buffer ownership and versioning;
adding an operation needs a new compatible tail field or a new ABI version.

## Frozen C ABI v1 foundation

The normative foreign header is
`src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h`.
It fixes structure widths and sizes, pointer-plus-length borrowed inputs,
provider-owned outputs, and typed entry/open/compile/finalize/diagnostics/
close/release signatures. The library lease outlives every descriptor, vtable,
session, and buffer. ABI or structure mismatch fails before `open_session`.

This completes only the ABI foundation. Production descriptor decoding,
canonical MIR serialization, session integration, and `--backend-plugin`
activation remain pending.

Current status: native lifecycle, Simple canonical-MIR transport, CLI/cache
path policy, and provider-content identity are implemented. Interpreter extern
dispatch and admitted dynamic session activation remain pending. Phase 3
convergence is not established.

## V1 baseline, `SBH1` AOT parity, and capability attestation (2026-11-18)

Per `doc/03_plan/compiler/phase3_first_dynlib_architecture_bootstrap_2026-11-18.md` (`C3`, `C4`), dynamic provider rollout reuses the frozen V1 foreign C ABI (`simple_backend_plugin_v1`) first and closes three architectural gaps before expanding target/ISA variants:

- **V1 baseline & host/target separation:** The first dynamically packaged provider (`W3` / `G-DYN-ONE`) targets the feature-free host baseline through `simple_backend_plugin_v1` (`SBQ1` request envelope, staged SHA-256 provider lease, process/session-retained lifetime). Manifests and admission keep **compiler host ABI** (the `.dll`/`.so`/`.dylib` binary loaded into the compiler process, including Windows GNU/UCRT vs MSVC CRT boundaries) separate from **emitted target triple/CPU/features**.
- **`SBH1` AOT admitted-handle parity:** `DynamicBackendAdapter.compile_aot_into_path` routes through `lease.begin_admitted_call()` + `backend_plugin_run_admitted_module_v1` (`SBH1` handle wire in `runtime_backend_plugin.c`) + `lease.end_admitted_call()`, matching `compile_module` and `compile_module_batch` instead of reopening `provider_path` by filesystem path. Closed or revoked leases are rejected deterministically.
- **AOT request parity validation:** `backend_plugin_aot_request_parity_diagnostic_v2` (`target_context_v2.spl`) verifies that AOT call-site parameters (`opt_level`, `target_cpu`, `storage_bindings`, plus `is_release` when an explicit profile-qualified optimization selector constrains `debug` vs `release`) agree with the admitted `BackendPluginRequestV1`, keeping `is_release` orthogonal to `o0..o3` while failing closed with `PLUG-E-CONFIG-MISMATCH` on mismatched overrides.
- **Feature attestation states (`Unknown` / `ConfirmedBaseline` / `ConfirmedFeatures`):** Synthetic V1 bridge descriptors in `loader.spl` remain `Unknown` (`BackendCapabilityAttestationKindV2.Unknown` / `BackendSessionFeatureAcceptanceV2.Unknown`), permitting only empty `request.features` and refusing nonempty CPU feature sets. Providers supplying explicit capability attestation resolve to `ConfirmedBaseline` (baseline-only confirmed) or `ConfirmedFeatures` (requested features verified against provider-supported features), and both `(feature_acceptance, accepted_features)` are bound into `_backend_session_result_envelope_sha256_v2` (`session_authority_v2.spl`) and `00.common/backend_plugin/receipt.spl`.

Status (2026-11-18): `C3`/`C4` source and unit specs (`test/01_unit/compiler/backend_plugin/{dynamic_aot_admitted_parity_spec,session_authority_v2_spec,target_context_v2_spec,loader_session_spec}.spl`) are `in-progress / unit-verified`; native `G-P3-HOST`, `G-DYN-ONE`, and `G-CONFIG` bootstrap/provider gates remain pending execution.
