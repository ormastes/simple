# Engine2D OpenCL Backend Facade Specification

> Manually synchronized on 2026-07-12 because executable Simple/docgen attempts
> were already exhausted for this session. This is static review material, not
> native execution or throughput evidence.

The nine scenarios cover generated OpenCL source, fail-closed initialization,
font composition, atlas invalidation, and mirror/device coherence. The atlas
upload scenario deterministically selects four dirty bytes only for a valid
generation `1 -> 2`; allocation, generation gaps, invalid rectangles, and empty
dirty metadata select the full-upload path. A conditional real-device scenario
preserves an old glyph after the dirty write and proves a `2 -> 4` gap refreshes
an atlas pixel omitted from dirty metadata.

Source: `test/01_unit/lib/gpu/engine2d/backend_opencl_facade_spec.spl`

