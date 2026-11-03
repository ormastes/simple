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
