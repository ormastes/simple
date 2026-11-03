# engine3d: `*_ext.spl` plain impl blocks are never imported — trait impls incomplete

Date: 2026-07-02
Status: open (CPU backend fixed; same latent bug in all other 3D backends)
Severity: P2
Found by: W6 lane agent

## Symptom

`error: semantic: type 'CpuBackend3D' does not implement required method
'create_texture_ex' from trait 'RenderBackend3D'`

The 3D backends split trait-required methods into sibling `*_ext.spl`
files containing plain `impl Backend:` blocks. Nothing imports those
files, so the methods never attach and the backend fails trait checking —
`std.gpu.engine3d` was completely uncompilable.

## Fixed

`gc_async_mut/gpu/engine3d/backend_cpu.spl`: 26 methods moved from
`backend_cpu_ext.spl` (deleted) into the real
`impl RenderBackend3D for CpuBackend3D` block.

## Still latent (same pattern, unverified/broken)

- `gc_async_mut/gpu/engine3d/backend_software.spl` / `backend_vulkan.spl`
  / cuda/rocm backends and their `*_ext.spl` siblings
- `gc_sync_mut/gpu/engine3d/backend_cpu_ext.spl`
- `nogc_sync_mut/engine/render/gpu_mesh3d.spl` also still declares the
  nonexistent `rt_f64_*` externs (fixed elsewhere as `rt_math_*`).


## Recovered Windows repair candidate (2026-11-03)

Owner: codex-engine3d-recovery-20261103. Isolated branch
`work/engine3d-trait-recovery-20261103`. This owner is **gc_async_mut**, so
this candidate belongs to the later other-libraries group after nogc_async_mut
and common in the requested Windows repair order. Draft candidate only; not landed.

SoftwareBackend3D, CudaBackend3D and RocmBackend3D each lacked 26 of the 74
RenderBackend3D methods, not merely the seven extended core texture methods.
All 26 existing methods move unchanged from each backend's plain sibling impl
into its primary `impl RenderBackend3D for ...` block. The extension modules become compatibility re-exports of their primary same-family
owners because gc_sync_mut facades still import those paths. Existing family selection
and generic imports remain unchanged; this does not globally pin gc/nogc owners.

Validation of the candidate: source structural checks PASS for all 74 trait
methods per backend, no duplicate primary method names, exact preservation of
all 26 moved signatures/bodies, and 26 omission negative controls per backend.
`git diff --check` passes. These checks establish source placement only.

New regression: `test/01_unit/lib/gpu/engine3d/backend_primary_trait_spec.spl`
imports only the three primary owners and checks names plus real fallback occlusion counts through a
RenderBackend3D-typed argument: empty framebuffer 0, two colored pixels 2,
partly clipped rectangle 1, fully outside rectangle 0. This uses fallback
framebuffer initialization without GPU hardware.
Behavioral status: **TEST_BLOCKED**; no qualified Pure-Simple runtime was
available. The Rust seed was not used. Compiler/lib/MCP/LSP gates and native
smokes remain unrun. No runtime or GPU functionality PASS is claimed.

Existing emu_create_texture_ex/create_sampler/etc providers still return
unsupported sentinels or no-op. Their semantics are preserved, not repaired;
this is trait completeness only. Other backend families/extensions in the
original report remain outside this candidate and the overall bug stays open.
Do not close the bug or land this later-family candidate before the earlier
requested Windows groups and parent review.

Parent review caught compatibility callers before PR: bounded owned-code rg
found gc_sync_mut/gpu/engine3d/backend_{software,cuda,rocm}_ext.spl importing
these paths. All three backing paths now remain as same-family re-exports;
no duplicate extension impls are retained. Existing storage-buffer emulation
is unsupported too, so the regression deliberately exercises the real
occlusion pixel loop rather than asserting placeholder buffer behavior.

## Canonical database reconciliation — 2026-11-03

OPEN umbrella; partial source candidate PR #6299 MERGED at 621609a09580be96d70467632df79d8efba1561c. Software/CUDA/ROCm trait methods and compatibility imports received source checks, but other backends and unsupported texture behavior remain outside the repair. TEST_BLOCKED: three behavioral occlusion cases and required core/native checks UNRUN. Await qualified runtime verification; no GPU qualification or umbrella closure.

## Remaining required trait owners — 2026-11-03 follow-up candidate

Session `p2-engine3d-ext-20261103` inspected release source after merged PR
#6299. Baremetal, Intel, OpenGL, Qualcomm, Virtio GPU and WebGPU still each
lacked 26 required RenderBackend3D methods in their primary trait block.
This candidate moves those 156 existing method signatures and bodies unchanged
into the six primary owners. All twelve primary backends now contain the
required method set in source. This is source trait completeness, not GPU
capability qualification.

Baremetal/Intel/OpenGL/Qualcomm/Virtio extension paths remain compatibility
re-exports, including their existing gc_sync_mut facades. The gc_sync_mut CPU
extension facade now targets the real primary CPU owner instead of the deleted
CPU extension. WebGPU retains its 21 optional extension methods and explicit
Engine3DExtended import; this change does not attach or implement its optional
GPU features. Existing unsupported providers and other optional extensions
retain their previous behavior. No configured family selection is changed.

Scoped source verification: six owners contain all 74 required methods with
no duplicate method names; 156 moved signatures/bodies are preserved and 156
single-method omission negative controls detect the missing requirement.
WebGPU's 21 remaining optional method bodies are preserved. Each modified
primary owner stays below 800 lines.

`backend_remaining_primary_trait_spec.spl` adds six primary-only admission
cases with actual fallback occlusion counts 0/2/1/0. The separate
`backend_extension_compatibility_spec.spl` adds six CPU and sync-extension
import controls so those imports cannot mask a broken primary-only case.
These twelve authored behavioral cases are **TEST_BLOCKED**, with zero tests
executed: no qualified self-hosted CLI is available. Required compiler/lib/
MCP/LSP checks and native smokes are likewise unrun; no seed fallback or runtime
PASS is claimed. The umbrella remains open pending those gates and parent review.
