<!-- codex-research -->
# GUI Color/Image Pipeline 8K Domain Research

Date: 2026-05-31

## Sources Checked

- W3C CSS Color Module Level 4, Candidate Recommendation Draft, 2026-05-02:
  https://www.w3.org/TR/css-color-4/
- TIFF Revision 6.0, Final, 1992-06-03:
  https://www.itu.int/itudoc/itu-t/com16/tiff-fx/docs/tiff6.pdf
- ISO/IEC 18181-1:2024 JPEG XL core coding system:
  https://www.iso.org/standard/85066.html
- libjxl color management API:
  https://libjxl.readthedocs.io/en/latest/api_color.html
- libjxl decoder color profile API:
  https://libjxl.readthedocs.io/en/latest/api_decoder.html

## Findings

- CSS Color 4 makes device-independent Lab/LCH and predefined XYZ spaces first
  class web color syntax. It also defines `xyz-d50`, `xyz-d65`, and `xyz` as
  predefined color spaces, and explains that XYZ is additive/linear-light while
  most RGB spaces need linearization before physically meaningful mixing.
- CSS Color 4 warns that wide-gamut/internal precision must be high enough for
  round trips; half-float or float internal storage is recommended for wide-gamut
  internal color values, but this does not imply full-frame float storage for
  every render target.
- TIFF 6.0 has explicit CIE L*a*b* image support. It describes Lab as
  colorimetric, with separate lightness and chroma channels, approximately
  perceptually uniform, and useful for device-independent continuous-tone image
  editing. It also notes Lab derives from CIE XYZ and that Lab-to-RGB conversion
  is required for display.
- TIFF 6.0 also states that full-color images encoded directly in linear spaces
  such as RGB or especially XYZ need very large data ranges. That supports using
  XYZ as a connection/conversion space, not as the default packed framebuffer.
- JPEG XL ISO/IEC 18181-1:2024 is a published international standard for
  compressed bi-level, grayscale, continuous-tone color, or multichannel images.
  Pure Simple support should therefore be treated as a full codec project, not a
  small parser.
- libjxl exposes the shape a performant color system should mimic: parse color
  profiles, initialize transforms with thread count and pixels-per-thread, and
  run conversion in chunks. This maps well to Simple tile conversion and lazy
  per-surface transform caches.
- libjxl decoder guidance distinguishes encoded structured profiles and ICC
  profiles. When ICC-based color management is used, callers generally ask for a
  ready-to-use ICC profile, while structured color metadata remains useful for
  nominal color-space decisions. Simple should keep both a structured color
  description and optional profile payload in image metadata.

## Recommendation

Use CIELAB as the default semantic/perceptual color API for theme colors,
gradients, interpolation policies, image metadata comparisons, and perceptual
diagnostics. Use CIE XYZ D50/D65 as the connection space for conversions. Keep
the default 8K framebuffer as packed 32-bit premultiplied color, with Lab/XYZ
conversion performed lazily and tile-locally.

Do not switch the whole library set at startup or init. Add per-surface,
per-document, and per-image policy selection. Initialize codec/color transforms
only when a document or asset requires TIFF, JPEG XL, Lab, XYZ, wide gamut, HDR,
or ICC handling.

## 2026-05-31 Codex Refresh

Additional source check:

- CSS Color 4 keeps Lab/LCH defined relative to D50-adapted XYZ and keeps
  `xyz-d50`/`xyz-d65` explicit, so Simple should not collapse Lab and XYZ into
  one storage format.
- ICC v4 still treats PCS Lab and PCS XYZ as interchange encodings tied to the
  profile connection workflow. ICC parsing should stay asset/profile scoped and
  cached after first use rather than loaded globally.
- BigTIFF/libtiff practice confirms that broad TIFF support means a matrix of
  byte order, strips/tiles, planar/chunky, sample widths, compression, alpha,
  and ICC tag handling. The current pure Simple baseline-strip decoder is the
  right first stage, but not a complete TIFF claim.
- JPEG XL color handling includes structured color encodings and ICC payloads,
  while pixel decode splits into VarDCT and Modular paths with extra channels
  and progressive features. Pure Simple support should keep metadata and small
  codestream parsing separate from full pixel decode milestones.

Refined recommendation: keep one hot render representation for UI frames:
premultiplied 32-bit packed pixels. Use CIELAB as the default public semantic
color model, CIE XYZ as the conversion/PCS model, and initialize TIFF/JPEG XL
decode stages plus ICC/Lab/XYZ transform kernels lazily per asset, surface, or
document. Whole-library startup switching would increase cold-start time and RSS
for the common sRGB path while giving no hot-frame benefit.

## 2026-05-31 Codex Object-Evidence Refresh

Additional source check:

- W3C CSS Color 4 continues to expose Lab/LCH and XYZ-family spaces as web color
  syntax, which supports keeping CIELAB as the public semantic color space and
  CIE XYZ as an explicit conversion space instead of treating them as one
  framebuffer format.
- TIFF 6.0 includes CIELAB image support and profile-oriented full-color use
  cases, but its broad surface area means production support has to be proven by
  pixel fixtures across strips, tiles, planar/chunky samples, PackBits, palette,
  high-bit-depth, alpha, and Lab conversion.
- libjxl decoder APIs expose ICC/structured color profile handling separately
  from pixel decode. That supports the current staging split: metadata/color
  profile detection first, followed by explicit Modular and VarDCT pixel-decode
  milestones before claiming full JPEG XL rendering support.

Current evidence implication: TIFF has real pure Simple pixel raster coverage in
the browser paint path. JPEG XL support is still limited to format detection,
dimension metadata, color metadata planning, and exact placeholder raster
behavior; full JPEG XL pixel decode must remain visible as unfinished work.
