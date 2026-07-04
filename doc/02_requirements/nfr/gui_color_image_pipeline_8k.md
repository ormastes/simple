# GUI Color/Image Pipeline 8K NFR Requirements

Date: 2026-06-01

Selected option: Option A, 8K packed hot path with lazy wide-color work.

## Requirements

- NFR-GCI8K-001: A single 7680x4320 32-bit framebuffer must remain about 126.6 MiB, reported exactly as 132,710,400 bytes in evidence.
- NFR-GCI8K-002: Default sRGB pages and default 8K surface plans must not allocate full-frame Lab/XYZ float buffers.
- NFR-GCI8K-003: Startup and 8K surface planning must initialize zero TIFF decoders, JPEG XL decoders, ICC/profile transforms, and Lab/XYZ transform caches unless an asset or operation requires them.
- NFR-GCI8K-004: First-use color/profile/codec work must expose evidence for initialization state and, where implemented, timing/cache/RSS or tile-count diagnostics.
- NFR-GCI8K-005: Native codec or color libraries may be used only as diagnostic or performance references; accepted functionality must have a pure Simple implementation path.
- NFR-GCI8K-006: Exact-pixel and checksum evidence must remain deterministic across reruns and must explicitly record that blur/tolerance matching was not used.
- NFR-GCI8K-007: Unsupported high-bit-depth, compressed raster, ICC, or JPEG XL subsets must fail closed within bounded time and memory rather than falling back to placeholder success.

## Deleted Options

Options B and C from the options document are not selected. Do not accept always-on wide-color full-frame buffers or native-bridge-only codec support as satisfying this NFR set.
