# CUDA compiler backend placement is not selectable

Status: **OPEN**. User selected static, dynamic, and disabled CUDA modes on
2026-10-10. This record proves source wiring gaps, not runtime qualification.

Reviewed source: `c6f5fc3f5643cea498d860189fc33445a971b293`.

## Actual boundaries

`src/plugins/backend_registry/full_static_backend_registry.spl` imports the
full port table and unconditionally registers `BackendKind.Cuda` with
`BackendLinkClass.PluginStatic`. `full_static_backend_ports.spl` imports
`plugins.backend_cuda.cuda_backend.CudaBackend`; its CUDA port advertises
`emit-gpu` and returns `CodegenOutput.GpuCode`. Selecting LLVM for a command
does not remove this compiler composition dependency.

`src/compiler/80.driver/driver_backend_plugin_selection.spl` explicitly returns
false for `cuda` and `ptx` in `driver_aot_uses_versioned_backend`.
`driver_aot_native_output.spl::compile_to_native` opens the versioned session
only when this predicate is true. Consequently an existing generic
`--backend-plugin` option is not proof of dynamic CUDA routing.

The canonical compiler dynamic loader is
`src/compiler/70.backend/backend_plugin/loader.spl::load_backend`, which routes
an explicit plugin path through the checked `DynamicBackendPluginLease` and
exact `simple_backend_plugin_v1` symbol. The current common capability model
has `ObjectEmit`, no GPU-output capability, and a `finalize_object` operation.
Merely changing the CUDA predicate would incorrectly promise the object ABI.

Runtime GPU provider loading (`gpu_dynamic_backend_full_offload.md`) is a
different boundary. Aspect dynamic loading admits SMF `.aspect_pack` containers
and typed facets; it does not currently select a compiler CUDA backend.

## Smallest compatible correction

Use the canonical `simple.sdn` manifest and existing `BackendPortV1`,
`IfaceId`, and `ParamHeader` contracts. Reuse existing placement metadata where
applicable; do not reuse startup `load_policy` for this purpose: that field
selects mapping/read-ahead behavior, not provider enablement or link placement.

Generate a selected composition from enabled state and static/dynamic
placement. Move individual optional ports out of the all-provider import
module. Static CUDA retains its current port and implementation. Disabled CUDA
has no registration or implementation import and explicitly rejects a CUDA
request. Dynamic CUDA imports only the admission/transport owners and requires
an explicit provider artifact. Do not silently substitute static CUDA.

Before extending dynamic output, review an additive artifact-kind/capability
contract against the existing ABI and buffer lifecycle. Bind selected mode,
provider digest, ABI digest, target, and artifact kind into cache identity.
If exposed through aspect facets, use the same admitted provider lease and
quiescence contract; aspect admission cannot bypass backend admission.

## Required execution evidence

1. Static: compile a real MIR kernel to PTX, retain CUDA symbols/dependency.
2. Dynamic: load a built CUDA provider, emit PTX matching the static fixture;
   reject missing provider, wrong ABI, and wrong artifact capability.
3. Disabled: reject CUDA explicitly; inspect the source closure and linked
   symbols to prove CUDA implementation absence.
4. Test enabled/disabled and link-placement cache invalidation independently.
5. Exercise shared-library lifecycle through SoSix host facades on Linux,
   Windows, macOS, FreeBSD, and a truthful unsupported path for SimpleOS where
   the selected loading capability is absent.

None of these execution gates has passed in this review. The narrow CUDA
enum-pattern bootstrap workaround is independent and must retain static
support while this placement gap remains open.

## 2026-10-11 bounded correction

Selected source overlays, truthful static PTX port metadata/options, and early
disabled/dynamic/unselected request diagnostics are implemented in the CUDA
policy branch. The focused native policy probe passes. Dynamic GPU artifact ABI,
full disabled closure/symbol proof and broad compiler verification remain open.
See [seven-plan evidence](../../03_plan/evidence/seven_plans/cuda_plugin_policy_audit_2026-10-11.md).
This update does not change the OPEN status or certify host completion.
