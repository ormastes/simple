# Metal Font Atlas Companion Specification

> Manually synchronized on 2026-07-12; no Simple/docgen or native Metal command
> ran in this session.

Five scenarios verify the exact 13-word/52-byte little-endian parameter block,
signed-coordinate overflow rejection, the initial invalidated atlas state,
failed zero-prefix preservation of device framebuffer truth, and native-only
typed Metal routing. Runtime pipeline and device-readback acceptance remain
macOS integration evidence.

Source: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl`
