# Pure Simple Vulkan image-upload staging scratch (2026-09-10)

Status: implemented; admitted-device timing remains pending provider authority.

## Baseline

The production batched image path is
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` ->
`backend_vulkan_helpers.spl` -> the Vulkan SFFI. Commit `3327c7511bf` already
removed one device-buffer allocation/free per image by retaining fenced source
buffers in a bounded per-surface pool. Its structural report records the
remaining cost: every image draw still creates a fresh `[u8]` pixel payload
before the host-to-device upload.

## Change

Each Vulkan surface now retains one bounded host upload scratch array (maximum
64 MiB). Image pixels are packed into that array in place. Native array-ABI
lanes call the Pure Simple `vulkan_sffi_copy_to_buffer_prefix` facade with the
initialized byte count, so a larger retained scratch does not upload stale
tail bytes. Interpreter array-ABI lanes fail closed when the prefix is not the
whole array and use the existing exact-size conversion/upload path. Images
above the bound also retain the exact-size path.

The prefix facade rejects non-positive lengths, negative offsets, prefixes
longer than the provided array, and signed offset/length overflow before
crossing the ABI. Image uploads are four-byte aligned by construction
(`pixel_count * 4`, offset zero). Zero-sized images remain rejected by the
existing image-path preflight rather than being reported as GPU work.

This removes repeated host-array allocation for repeated or smaller image
sizes after the scratch has reached sufficient capacity, without changing
upload bytes, device-source ownership, descriptor
lifetimes, command batching, or fence behavior. The staging array is a CPU
marshalling object; it is not reused as a GPU dependency. Device source
buffers remain protected by the existing pending-dependency table and exact
fence/device-idle cleanup.

The mutable `VulkanBackend` remains the sole surface owner. Packing and the
synchronous host-to-device snapshot contain no suspension or callback point,
so the scratch cannot be re-entered between initialization of its prefix and
the upload. The facade reuses the canonical, pre-existing
`rt_vulkan_copy_to_buffer_array` declaration already used by the legacy native
upload selector; it introduces no new native symbol or loader obligation.

## Structural evidence

| Path | Before | After |
|---|---|---|
| repeated native image upload | allocate/pack a new `[u8]` payload per draw | pack in one retained per-surface scratch; upload only initialized prefix |
| interpreter or oversized image | exact-size conversion/upload | unchanged exact-size conversion/upload |
| GPU source buffer | fenced image-source pool from `3327c7511bf` | unchanged; scratch reuse never bypasses its fence gate |
| retained host memory | no staging bound | one scratch array, capped at 64 MiB |

Owner-side counters are `image_upload_scratch_reuse_count`,
`image_upload_scratch_resize_count`, and
`image_upload_scratch_fallback_count`. They are structural observability only;
the reuse count advances only after a successful prefix upload actually avoids
the legacy exact-size allocation. They do not claim physical GPU execution or
a performance pass. The host-only scratch is cleared before any shutdown
quarantine early return; it never participates in device/session/surface/fence
ownership.

## Verification

- Contract: `test/01_unit/check/vulkan_engine2d_image_upload_scratch_contract_spec.spl`
- The stale pool-contract string expectation was updated to match the existing
  line-wrapped ownership guard without weakening its predicate.
- `git diff --check`: PASS.
- Static target-source review: PASS for the production call chain, 64 MiB
  retained bound, initialized-prefix upload, exact fallback, overflow and
  alignment guards, successful-reuse counter semantics, early shutdown
  release, and unchanged device/fence ownership.
- O3 and executable SPipe remain blocked: `bin/simple` resolves to the Rust
  bootstrap seed, which explicitly refuses production-tool status; the one
  focused contract attempt was killed by the existing bounded test-runner
  wrapper before assertions completed. No retry or seed PASS is claimed.
- Hardware timing, C Vulkan/Simple comparison, Chrome comparison, and Stage-2
  admission: not claimed here.
