<!-- codex-research -->
# GUI Color/Image Pipeline 8K Feature Options

Date: 2026-05-31

## Option A: Lazy Color/Image Pipeline With Packed 8K Framebuffer

Description: Keep the hot render target as packed premultiplied 32-bit
ARGB/RGBA. Add CIELAB and CIE XYZ value types, color conversion helpers, image
metadata/profile structures, and pure Simple TIFF/JXL decoder milestones behind
lazy per-surface/per-asset policy. Web rendering and Simple browser consume the
shared image facade.

Pros:
- Preserves current exact-pixel and performance lanes.
- Avoids startup delay for pages that use only sRGB/packed assets.
- Fits 8K memory constraints.
- Lets TIFF/JXL land incrementally with fail-closed unsupported subsets.

Cons:
- Requires careful metadata propagation through web renderer, browser, and WM.
- Requires tile conversion infrastructure and transform cache invalidation.

Effort: L. Expected 20-35 files across color, image, web render API, browser
image loading, specs, reports, and codec fixtures.

## Option B: Global CIELAB Working Mode

Description: Switch the GUI/web renderer library set at startup into CIELAB as
the default full-frame working representation, converting to RGB only at
presentation.

Pros:
- Simple conceptual model for perceptual color operations.
- All render stages see the same semantic color space.

Cons:
- High startup/RSS cost and likely 8K performance regression.
- Full-frame float Lab/XYZ intermediates are too large for routine 8K use.
- Risks breaking existing exact bitmap parity and ARGB checksum gates.

Effort: XL. Expected 35-60 files and broad renderer rewrites.

## Option C: Codec-Only Support Without Color Pipeline

Description: Add TIFF and JPEG XL decoders that output packed sRGB/ARGB only,
without first-class Lab/XYZ/profile handling.

Pros:
- Smaller first implementation.
- Faster path to displaying some TIFF/JXL assets.

Cons:
- Does not satisfy CIELAB default or CIE XYZ support.
- Would lose color metadata needed for web/browser correctness.
- Likely creates technical debt in image decode APIs.

Effort: M/L. Expected 12-25 files, but with later redesign risk.

## Recommendation

Choose Option A.

