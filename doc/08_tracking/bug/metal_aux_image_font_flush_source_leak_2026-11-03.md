# Metal auxiliary image leaks its source buffer when font flush fails

Status: source repair prepared; runtime verification not performed (user waiver).

`_dispatch_metal_indexed_fill` and `_dispatch_metal_glyph_atlas_blit` allocate a
per-call source buffer and transfer ownership to
`MetalBackend._dispatch_metal_aux_image_checked`. The helper releases that
buffer on command allocation, encoding, pending-command, and completed-submit
paths. Its initial `font.flush() < 0` return omitted the release. The caller
only frees parameter storage, so a failed font submission leaked the fresh
source buffer.

The failure path now releases the source before returning, invalidates the
GPU frame, and records the preceding font failure. Parameters and the
persistent auxiliary LUT remain caller-owned. No auxiliary command has been
created at this point, so this source has not been submitted to the device.

Missing regression: inject a failing deferred-font submission after the
indexed-fill or glyph caller allocates its source, then observe one release
of that source, no release of params or the persistent LUT by this helper,
and a false result with an invalid GPU frame. The current helper directly
uses the Metal provider and exposes no allocator/submission injection seam.
No source-text assertion is offered as a substitute for that device test.
The diagnosis is static source evidence, not a reproduced GPU failure.
