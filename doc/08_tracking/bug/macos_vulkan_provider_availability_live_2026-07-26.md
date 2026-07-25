# macOS Vulkan live backend is unavailable before rendering

## Status

Open. The current trusted self-hosted Vulkan harness rebuilds, but no current
framebuffer or event capture exists.

## Evidence

- The canonical live checker launched the current stripped manifest artifact
  and failed before readiness with `launched-process-missing`.
- Direct execution of that artifact returned `132` and printed
  `runtime error: field access on nil receiver`.
- A current unstripped diagnostic build reached the explicit backend receipt
  instead of the receiver trap:

  ```text
  gpu_2d_live_status=fail
  gpu_2d_live_reason=backend-create-failed
  gpu_2d_live_requested_backend=vulkan
  gpu_2d_live_selected_backend=cpu
  gpu_2d_live_probe=Vulkan shared session initialization failed: availability
  ```

The provider dylib exports `rt_vulkan_init`,
`rt_vulkan_provider_is_available`, and `rt_vulkan_provider_device_count`;
MoltenVK and the Vulkan loader are installed at the configured Homebrew
paths. Symbol presence therefore does not prove runtime provider admission.
The stripped/unstripped divergence also means the nil receiver must not be
treated as the sole cause.

## Next discriminator

Add a focused provider probe that records availability, device count, loader
path, and provider error before constructing `VulkanBackend`. Run it against
the exact provider dylib linked by the manifest, then fix provider admission
or the native receiver/cache divergence before spending another full live
window cycle.

The three Vulkan build/launch diagnosis cycles for this session are exhausted.
