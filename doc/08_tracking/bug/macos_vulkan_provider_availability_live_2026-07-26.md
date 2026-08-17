# macOS Vulkan live backend is unavailable before rendering

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## Focused provider micro-probe — 2026-07-26

A separate windowless discriminator now exists at
`scripts/check/check-macos-vulkan-provider-micro-probe.shs`. Its pure-Simple
probe opens one explicitly supplied provider dylib and directly resolves:

- `rt_vulkan_provider_is_available`
- `rt_vulkan_provider_device_count`
- `rt_vulkan_init`
- `rt_vulkan_get_last_error`
- `rt_vulkan_shutdown`

The checker requires a trusted compiler manifest binding the canonical path and
SHA-256, and records bounded, hashed provider/build/probe evidence. It does
not construct `VulkanBackend`, start Engine2D, use winit, or launch a window.

The focused source contract passed 2/2. The only allowed native execution
attempt did not reach the provider: the canonical self-hosted compiler exited
with `Illegal instruction: 4`, and its retained build log contains:

```text
runtime error: field access on nil receiver
```

`DynLib.call0` only exposes an i64 ABI, while the resolved
`rt_vulkan_get_last_error` symbol returns text. The probe therefore reports a
blocked dynamic-text ABI instead of unsafely calling it. Provider availability,
device count, dyld resolution, and provider error remain unobserved in this
run. No Rust seed fallback and no exhausted full-live Vulkan command were used.
