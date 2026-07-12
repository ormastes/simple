# Metal Font Atlas Companion Specification

> Manually synchronized on 2026-07-12; no Simple/docgen or native Metal command
> ran in this session.

Seven scenarios verify the exact 13-word/52-byte little-endian parameter block,
signed-coordinate overflow rejection, the initial invalidated atlas state,
sequential distinct-renderer dependency tokens do not alias cached Metal atlas
state under serialized access,
unsupported program versions fail before atlas mutation, failed zero-prefix
preservation of device framebuffer truth, and native-only typed Metal routing.
Runtime upload, pipeline, and device-readback acceptance remain macOS
integration evidence. Concurrent token allocation and renderer ownership remain
unsupported.

Source: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl`
