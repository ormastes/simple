# Bootstrap dynload provider qualification gap

Status: OPEN. Production provider packaging/load verification is incomplete.
Canonical derived bug-database reconciliation: pending; this report alone is
not a successful database refresh or a backend qualification receipt.

## Observed boundary

The Windows bootstrap candidate derived from `07d01763de6` contains the
versioned provider ABI, runtime bridge, loader, built-in adapters and dynamic
provider fixtures. Owned-source searches for `simple_backend_plugin_v1` found
the declaration/lookup/fixture entry points, but did not locate an actual LLVM
or Cranelift production provider export/build target. This search is discovery
evidence, not proof that no generated export can exist.

The repaired Rust seed explicitly rejects dynload packaging with
`E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED`. Its single output is a bootstrap
prerequisite; it cannot qualify the requested dynamic backend artifacts.

In `src/app/cli/bootstrap_focused_native_build.spl`,
`run_exact_stage3_focused_capsule` requires the `dynload` mode string, while
`run_focused_native_build_plan` validates it and calls
`aot_native_project_with_backend_fixed` without a mode/packaging argument.
Acceptance of this string is therefore insufficient evidence of a loaded
backend provider. Stage 4's explicit one-binary full-CLI route is a separate,
intentional product mode and is not itself this defect.

## Required repair and proof

Follow the selected contract in
`doc/03_plan/versioned_codegen_backend_plugin.md`; do not invent a second ABI.
Locate or implement each real provider build target, retain the checked
library/session lease, and verify descriptor, target, MIR ABI and capabilities.
Compile and run representative output through both loaded providers, including
the six compiler/interpreter/loader test binaries and their actual registries.
Bind artifact/cache receipts to provider identity and bytes. Missing providers
must remain explicit failures, without a silent built-in backend substitution.

Continue independent local bootstrap diagnosis with truthful single-artifact
lineage while this work remains open. Do not rename that result dynload, claim
provider reuse from a mode flag, or treat fixture DLL success as a production
backend qualification.

## 2026-11-18: Host-only composition & V1 dynlib AOT/attestation prerequisites (`C1`, `C3`, `C4`)

Status remains **OPEN**: production shared-library provider build, admission, emit, link, and execution receipts (`G-DYN-ONE` and later per-provider gates) are still required before closing this gap.

Progress recorded in `doc/03_plan/compiler/phase3_first_dynlib_architecture_bootstrap_2026-11-18.md` (`W1`, `W3`, `W4` / slices `C1`, `C3`, `C4`):

1. **Mode vs plugin disambiguation (`bootstrap_build_modes.md`, `build.md`):** Explicitly separated `--mode=dynload` (SMF+native output packaging) from `--backend-plugin=PATH` (`simple_backend_plugin_v1` shared-library codegen provider loading) and separated compiler host ABI from emitted target triple/CPU/features.
2. **Host-only closure + explicit `--backend-plugin` reachability (`C1`):** Added `SIMPLE_BACKEND_COMPOSITION=host-only|full` (`static_backend_registry.spl`), `src/compositions/backends_host_only` overlay, and explicit `plugin_path` request forwarding in `src/app/cli/bootstrap_essential_backend_request.spl` so a host-only Phase-3 compiler excludes static `plugins.backend_*` closures while still admitting an explicit `--backend-plugin` shared library without silent static fallback (unit spec: `test/01_unit/compiler/backend/host_only_composition_static_parity_spec.spl`).
3. **`SBH1` AOT admitted-handle parity, AOT request parity, and honest feature attestation (`C3`, `C4`):**
   - Switched `DynamicBackendAdapter.compile_aot_into_path` (`dynamic_adapter.spl`) from legacy path reopen to `lease.begin_admitted_call()` + `backend_plugin_run_admitted_module_v1` (`SBH1` handle packet) + `lease.end_admitted_call()`.
   - Added `backend_plugin_aot_request_parity_diagnostic_v2` (`target_context_v2.spl`) to reject mismatched AOT `(opt_level, target_cpu, storage_bindings)` overrides (plus `is_release` when an explicit profile-qualified optimization selector constrains `debug` vs `release`, while keeping `is_release` orthogonal to `o0..o3`) with `PLUG-E-CONFIG-MISMATCH`.
   - Distinguished unattested V1 bridge descriptors (`Unknown`, rejecting nonempty CPU features) from provider-confirmed capability attestation (`ConfirmedBaseline` / `ConfirmedFeatures`) bound into `_backend_session_result_envelope_sha256_v2` and `00.common/backend_plugin/receipt.spl` (unit specs: `test/01_unit/compiler/backend_plugin/{dynamic_aot_admitted_parity_spec,session_authority_v2_spec,target_context_v2_spec,loader_session_spec}.spl`).

Remaining native proof before closing: pass `G-P3-HOST`, package at least one real host-executable debug provider exporting `simple_backend_plugin_v1`, run the full `build dynlib -> admit -> open_session -> compile -> finalize -> link -> execute -> release/close` chain (`G-DYN-ONE`), and qualify the full declared Phase-4 provider catalog with artifact/receipt hashes.
