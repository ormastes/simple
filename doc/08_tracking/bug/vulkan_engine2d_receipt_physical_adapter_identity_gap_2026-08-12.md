# Vulkan Engine2D receipt physical-adapter identity gap

## Status

Open. Native Vulkan 8K measurements remain unqualified until a successful
Engine2D submission and its swapchain presentation carry one immutable,
physical-adapter receipt. This is a provenance issue, not a throughput result.

## Current evidence and gap

The runtime already exposes selected physical-device metadata:

- `rt_vulkan_selected_device_name()`;
- `rt_vulkan_selected_device_type()`;
- `rt_vulkan_selected_device_driver_identity()`;
- `rt_vulkan_selected_device_driver_identity_hash()`.

`VulkanSession` also captures name/type/driver identity while it initialises.
However, `Engine2dDrawIrAdvResult.device_identity` is not an adapter identity:
it comes from `VulkanSession.device`, whose `rt_vulkan_get_device()` currently
returns `1` whenever the canonical Vulkan state has a device. A receipt with
`device_identity=1` therefore proves neither adapter selection nor identity.

The existing winit presenter creates a surface-capable presentation device and
adopts it before Engine2D starts. `VulkanSession.init()` then selects adapter
index zero through the global runtime. The swapchain transfer safely rejects a
buffer from another `VulkanDevice`, but the successful receipt currently does
not record the presenter adapter, the Engine2D buffer adapter, or equality
between them. Global selected-device telemetry alone is insufficient because
it can be observed after another selection.

## Required receipt seam

1. In `src/compiler_rust/runtime/src/value/gpu_vulkan/vulkan_sffi/swapchain.rs`,
   expose presenter-handle accessors derived from the registry-owned
   `Engine2dPresenter.device`: adapter name, type, driver identity, and stable
   positive driver-identity hash. They must query that exact `Arc<VulkanDevice>`
   rather than global `STATE.device`.
2. Add matching narrow facade methods to
   `src/lib/nogc_sync_mut/gpu/engine2d/vulkan_presenter.spl`. A closed or
   invalid presenter yields an empty/zero receipt.
3. Add a versioned `VulkanEngine2dPresentReceipt` after presentation succeeds
   (status >= 0), with presenter handle, framebuffer handle, mode/revision,
   adapter name/type/driver identity/hash, and an explicit
   `same_adapter=true` only when the Engine2D framebuffer owner and presenter
   owner are the same `Arc<VulkanDevice>`. Do not infer equality from logical
   handle value or adapter index.
4. Propagate that receipt through `Engine2dCompositorBackend.present_device_frame`
   and the hosted/showcase receipt string. Extend `Engine2dDrawIrAdvResult`
   only with append-only fields if submit-side metadata is needed; its existing
   `device_identity` remains a compatibility token and must not be relabelled
   as physical identity.
5. Make the native 8K harness reject a row unless the submission fence, device
   present, non-empty physical adapter identity, positive hash, and exact
   framebuffer/presenter ownership equality are all present. CPU, virtual,
   and software adapters may be reported but cannot satisfy a hardware 8K/80
   row.

## Focused acceptance test

Add a native-only existing-window Vulkan integration scenario which:

1. Opens a winit-backed presenter, creates Engine2D Vulkan after it, submits
   one no-readback DrawIR frame, then presents it.
2. Requires `device_submit_count == 1`, `device_fence_count == 1`, successful
   presentation, a non-empty presenter driver identity, and hash > 0.
3. Requires `same_adapter == true`; force a foreign Engine2D buffer/device and
   require present failure with no success receipt.
4. Repeats a retained frame and requires the same immutable adapter receipt.
5. Runs only from a freshly published self-hosted compiler/runtime authority;
   a Rust seed, interpreter fallback, or prebuilt stale runtime is a skip/fail
   for native evidence and cannot close this issue.

## Stale-artifact dependency

Current source contains the missing `rt_struct_receiver_valid` registration,
but the live native Engine2D gate used stale compiler/runtime artifacts. See
`vulkan_engine2d_native_jit_missing_rt_struct_receiver_valid_2026-08-12.md`.
Publish a current self-hosted authority before exercising this receipt test;
otherwise a JIT fallback cannot prove the ABI or native execution path.

## Non-claim

This tracker establishes required adapter provenance only. It provides no
native execution, physical-GPU, resolution, p50/p95, or 8K/80 performance
claim.

## Source implementation update (2026-08-12)

The presenter registry now snapshots a driver-qualified physical-adapter
identity and stable positive tag from its exact `VulkanDevice`. Its present,
retained-present, and damage-present entry points first require the Engine2D
framebuffer to belong to that same device, before image acquisition or copying.
The canonical no-GC Simple facade exposes one receipt with that identity and
ownership status; the hosted compositor refuses invalid receipts and includes
valid identity/ownership fields in frame provenance.

The focused structural contract passes 3/3, and an isolated
`cargo check -p simple-runtime --features vulkan` passes (only the existing
winit `EventLoop::run` deprecation warning). Native live validation remains
blocked until a current self-hosted compiler/runtime authority is admitted and
published.
