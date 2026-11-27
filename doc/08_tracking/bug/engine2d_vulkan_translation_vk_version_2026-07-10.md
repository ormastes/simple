# Engine2D Vulkan Translation Requires Missing `vk_version` Argument
## Closed 2026-09-16 — ...lkanBackend.create()` to be mis-resolved to `compiler.backend.vulkan_backend.VulkanBackend

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Status

Open; blocks Linux DirectX-on-Vulkan and Metal-on-Vulkan RenderDoc capture.

## Reproduction

Run an injected RenderDoc producer that passes a runtime-selected backend text
to `Engine2D.create_requested_backend`, including:

```sh
SIMPLE_RENDERDOC_BACKEND=directx-on-vulkan \
  build/tools/renderdoc-linux-vulkan-only/bin/renderdoccmd capture ... \
  src/compiler_rust/target/release/simple run src/app/test/renderdoc_vulkan_capture.spl
```

The producer reports `requested_backend=directx-on-vulkan`, then fails before
rendering with:

```text
semantic: function expects argument for parameter 'vk_version', but none was provided
```

The same semantic failure occurs with runtime-selected `vulkan`, whereas the
canonical literal-Vulkan capture succeeds. This therefore blocks a dynamic
translation probe; it does not establish a failure of stored translation code.

## Root-Cause Direction

Literal `Engine2D.create_requested_backend(..., "vulkan")` succeeds in the
same process and capture command. Passing a runtime backend text causes
`VulkanBackend.create()` to be mis-resolved to
`compiler.backend.vulkan_backend.VulkanBackend.create(vk_version)`. This is
strong evidence of a runtime-dispatch/static-method resolution collision
across same-named classes, not a missing Vulkan device or RenderDoc capability.

An import-alias workaround was also rejected by the interpreter with
`unsupported path call: ["Engine2DVulkanBackend", "create"]`; the Engine2D
source was restored afterward. Fix the resolver key for imported static calls,
then add literal dedicated translation probes and rerun both explicit
translation rows.

## Impact

Native Linux Vulkan RenderDoc capture succeeds. Translation rows remain
host-supported-but-failing, never reported as native DirectX/Metal or passes.


## Triage 2026-11-25 (p3-bam lane, Windows worktree) — status header normalized, still environment-blocked

This record's headers disagree: the top line says "Closed 2026-09-16" (a
bookkeeping classification from the ledger normalization pass, explicitly
"not a re-run of the repro") while the Status section below still says
"Open; blocks Linux DirectX-on-Vulkan and Metal-on-Vulkan RenderDoc
capture." Neither is backed by an executed re-verification.

Triage disposition: **UNVERIFIED — environment-blocked.** The only faithful
repro requires a Linux host with RenderDoc (`renderdoccmd`), a Vulkan ICD,
and the engine2d capture pipeline; none of that exists on this Windows
verification host, and the mis-resolution (runtime-selected backend text →
`VulkanBackend.create()` binding to `compiler.backend.vulkan_backend`'s
`create(vk_version)`) is inside the same-named-class static-call resolver,
which cannot be exercised end-to-end without that pipeline. Per ledger rules
the entry is left as-is — neither re-opened nor confirmed closed. Read the
2026-09-16 "Closed" header as bookkeeping only; if the RenderDoc capture
lane is next exercised on Linux, re-run the dynamic translation probe and
record the result here.
