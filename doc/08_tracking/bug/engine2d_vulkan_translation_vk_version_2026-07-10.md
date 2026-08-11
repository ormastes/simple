# Engine2D Vulkan Translation Requires Missing `vk_version` Argument

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
