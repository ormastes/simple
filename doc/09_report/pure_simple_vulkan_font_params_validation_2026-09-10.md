# Pure Simple Vulkan font-parameter validation — 2026-09-10

## Scope

This slice removes an allocation from the reachable Pure Simple Engine2D
Vulkan font pre-flight path. It does not claim persistent host staging or a
packed-parameter upload optimization: the normal precompiled-SPIR-V and
runtime-GLSL routes use `vulkan_font_packed_params` and remain unchanged.

## Structural baseline

`VulkanBackend._composite_font_batch_impl` validates every quad before
selecting the artifact route. The previous validation call used
`vulkan_font_atlas_composite_params(...)`, which allocated a fresh 52-byte
array and packed all 13 words even though validation discarded the bytes. For
a batch with `N` quads this was one unnecessary host allocation and pack per
quad before the real packed frame payload was built.

## Change

`_vulkan_font_atlas_composite_params_valid` now contains the side-effect-free
range/product checks. The validation loop calls it directly, preserving every
rejection condition and the same `invalid-font-params` result. The allocating
encoder remains intact for the non-packed fallback route, and the packed frame
encoder remains the canonical production path.

This is a CPU-side pre-flight allocation/copy reduction only. No Vulkan ABI,
GPU buffer lifetime, descriptor binding, queue submission, fence, wait,
readback, or fallback ownership changed.

## Evidence

- Existing frozen ABI encoder still owns all 52-byte packed output for the
  non-packed route.
- Source contract pins direct scalar validation before packed payload creation.
- Existing parameter rejection cases remain covered by the font unit spec.
- `$optimize` O3 analysis completed for the touched font source.
- The multilingual GPU-font perf spec was attempted before this slice but timed
  out because the test daemon/self-hosted worker was unavailable; no timing row
  is claimed.
- Hardware Vulkan, admitted async-session, Chrome, and C comparison rows remain
  unavailable and are intentionally not claimed here.
