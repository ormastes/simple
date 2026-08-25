# std.gpu Context must not run a Vulkan request on CUDA

> Reproduce (2026-08-25): Context.new(backend: GpuBackend.Vulkan, ...) called

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.gpu Context must not run a Vulkan request on CUDA

Reproduce (2026-08-25): Context.new(backend: GpuBackend.Vulkan, ...) called

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/gpu_context_vulkan_honesty_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce (2026-08-25): Context.new(backend: GpuBackend.Vulkan, ...) called
gpu_cuda(device) in src/lib/nogc_sync_mut/gpu/context.spl (and an unimported
gpu_vulkan in the nogc_async_mut mirror), so a Vulkan request silently
reported a CUDA device. std.gpu has no Vulkan implementation; the real path
is std.gc_async_mut.gpu_lane.vulkan_*. Device-free.

## Scenarios

### std.gpu Context Vulkan requests

#### nogc_sync_mut: a Vulkan context has no CUDA device

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = SyncContext.new(backend: SyncBackend.Vulkan, device: 0)
expect(ctx.device_id()).to_equal(-1)
expect(ctx.is_cuda()).to_equal(false)
expect(ctx.backend_name()).to_equal("Vulkan")
```

</details>

#### nogc_async_mut: a Vulkan context has no CUDA device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = AsyncContext.new(backend: AsyncBackend.Vulkan, device: 0)
expect(ctx.device_id()).to_equal(-1)
expect(ctx.is_cuda()).to_equal(false)
```

</details>

#### None_ and Vulkan agree

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none_ctx = SyncContext.new(backend: SyncBackend.None_, device: -1)
val vk_ctx = SyncContext.new(backend: SyncBackend.Vulkan, device: 1)
expect(vk_ctx.device_id()).to_equal(none_ctx.device_id())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
