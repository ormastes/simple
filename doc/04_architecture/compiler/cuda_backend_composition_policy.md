# CUDA compiler composition policy

<!-- codex-architecture -->

Status: partial implementation, not release-qualified. Selected scope is static,
dynamic, and disabled CUDA, recorded in the
[selection gap](../../08_tracking/bug/cuda_backend_static_dynamic_disabled_selection_gap_2026-10-10.md).

## Compiler versus device capability

PTX emission accepts `cuda-ptx` and does not probe a CUDA driver or physical GPU.
Execution/device availability belongs to the runtime provider. PR #2840 changes
that runtime boundary; it does not supply a compiler GPU artifact ABI.

`src/plugins/backend_cuda/cuda_backend_port.spl` owns the static implementation
import. It preserves `BackendCompileOptions` and advertises GPU emission only.
The full registry combines its selected table with the non-CUDA ports. Unified
kernel emission uses the installed table, preserving OpenCL and VHDL output
when CUDA is unavailable and recording a PTX diagnostic.

## Manifest and generated source composition

`src/compiler/simple.sdn` contains `compiler_backends.cuda.enabled` and
`compiler_backends.cuda.placement`. The enabled boolean projects the existing
component presence meanings `on`/`off`; placement retains `static`/`dynamic`.
This is an explicit compiler-build schema, not the structural component loader.
The committed default is enabled/static. Missing values, duplicate keys,
unknown values, and `auto` are rejected. Generic component `auto` depends on
verified embedded/configured implementation digests; it is not an unconditional
static fallback and is not admitted by this compiler-build schema.

Bootstrap selects one committed template and copies it into a source overlay
whose path contains the compiler-manifest SHA256 and template SHA256. Seven
bootstrap/full-CLI/UI/MCP compile invocations receive that quoted source root.
Both enabled and placement changes therefore change the selected source/cache
identity, even when two settings select disabled mode. Existing generated
content is checked against its identity before use. No device-dependent build
choice or environment enablement override is added.

- Static: the selected table imports and registers the CUDA PTX port.
- Disabled: the selected table is empty and imports only common registry types.
- Dynamic: the selected table is empty; requests fail with
  `BACKEND_PLUGIN_GPU_ARTIFACT_UNSUPPORTED`. This is not working dynamic CUDA.

The full composition installs its mode once before CLI command dispatch.
Driver orchestration checks it before no-op/cache admission; direct native
compilation checks it again at its public entry. Disabled requests receive
`PLUG-E-DISABLED`; uninstalled/unknown composition receives
`PLUG-E-CUDA-POLICY`. Explicit CUDA/PTX provider paths cannot take a static
fallback. Other providers retain their existing admission behavior.

Standalone unified-emission callers must install a selected K1/full composition.
An uninstalled caller gets an explicit PTX diagnostic; it does not regain a
hidden static CUDA import. The existing unified system scenario now installs
its composition when needed.

## Remaining dynamic contract

Do not add GPU output to the existing `finalize_object` operation. An additive
versioned artifact interface must admit an artifact kind (PTX versus native
object), GPU-emission capability, target/SM version, ABI digest and MIR digest
before opening a retained provider lease. It needs a `finalize_artifact`
operation and an owned byte buffer released exactly once before lease teardown.
The current object V1 ABI must remain unchanged; negotiate a distinct exact
versioned symbol/interface for the new artifact operations.

Cache identity must bind mode, provider artifact digest, ABI digest, target,
artifact kind and compile options. Missing artifact, unsupported host loader,
wrong ABI/capability, teardown with live results and stale provider identities
must reject without substitution. Linux/Windows/macOS/FreeBSD provider lifecycle
and a truthful unsupported SimpleOS loading path remain execution gates.

## Verification boundary

The focused native policy executable and extracted production manifest selector
passed. Full disabled source closure and linked-symbol absence are still open;
compiler backend barrel reexports and separately compiled hosted GPU test-runner
children must be checked independently. Real static MIR-kernel-to-PTX execution,
static/dynamic parity, and broad compiler/MCP checks are not certified here.
See the [seven-item evidence](../../03_plan/evidence/seven_plans/cuda_plugin_policy_audit_2026-10-11.md).

Ownership: CUDA policy agent owns this change; bootstrap diagnostics agent owns
Phase 3/4 continuation. Merge owner and final reviewer: root agent. Sidecars N/A.

## Source precedence correction

The actual native disabled probe exposed a second closure traversal that ignored
explicit roots and reopened the default static module. Phase 1 now probes
ordered explicit source roots before its canonical checkout fallback. The
existing numbered-directory resolver still rejects ambiguous NN.name siblings.
The outer native-build source-root order already participates in its SCV key.
The change requires a newly built producer; the recorded producer still fails
the disabled closure gate.

## Ambiguous overlay authority

Exact-head review of the first draft found that an ambiguous numbered directory
was collapsed into the same empty string as a missing module. A later source
root or checkout fallback could then restore a default provider. The corrected
selected-root interface returns `Found`, `Missing`, or `Ambiguous` explicitly.
Numbered traversal propagates ambiguity through every path segment and stops
before another root or named-import suffix can be tried. The pipeline fallback
branch calls checkout resolution directly only for `Missing`; an ambiguity terminates
source loading with `SOURCE_ROOT_AMBIGUOUS`. Exact directories still take
precedence over numbered siblings, and relative imports stay importer-owned.
The older text-returning generic probe remains a compatibility boundary; the
selected-root path never calls that lossy wrapper.

The pipeline matches this enum directly. It does not pass checkout resolution
as a callback: that extra abstraction caused null function-pointer dispatch in
the integrated native compiler. Native verification must include the normal
missing-module path as well as selected and ambiguous overlays.

Actual native qualification shows this contract is not yet carried across the
outer scanner and worker boundary: the worker currently derives roots from
input files, and already-loaded names can skip selected authority checks.
Disabled and ambiguous CUDA requests still admit the default implementation.
The intended contract above is not an end-to-end completion claim; see
`doc/08_tracking/bug/source_root_worker_authority_gap_2026-10-11.md`.
