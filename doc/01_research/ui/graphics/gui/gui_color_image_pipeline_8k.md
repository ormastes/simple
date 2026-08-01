<!-- codex-research -->
# GUI Color/Image Pipeline 8K Local Research

Date: 2026-05-31

## Scope

Extend the active GUI hardening goal with 8K 32-bit full-color rendering, CIELAB
default color support, CIE XYZ support, pure Simple TIFF and JPEG XL decoding,
and integration with Simple web rendering and Simple browser image rendering.

## Current Repo Context

- The active GUI hardening state is `.spipe/gui-hardening-full/state.md`.
- Current exact-pixel evidence uses ARGB/u32 buffers through Engine2D,
  Electron bitmap checks, WM capture, PPM decode, and QEMU screendump decode.
- Existing image decode coverage is narrow: PPM and PNG appear in
  `src/lib/common/image/` and corresponding unit tests. TIFF and JPEG XL are
  not currently planned or implemented in the active state.
- Existing web-render shared API lives in `src/lib/common/ui/web_render_api.spl`
  and is the right integration boundary for image decode capability metadata,
  decoded image buffers, color profile metadata, and render-target policy.
- Current performance evidence is optimized around exact 8-bit ARGB checksums.
  That path should stay hot and stable for framebuffer presentation.

## 8K Memory Baseline

8K UHD is 7680 x 4320 = 33,177,600 pixels.

- 32-bit RGBA/ARGB framebuffer: 132,710,400 bytes, about 126.6 MiB.
- Double buffering: about 253 MiB.
- Triple buffering: about 380 MiB.
- Float XYZ or Lab full-frame storage at 3 x f32: about 380 MiB per frame before
  alpha, masks, or intermediate buffers.

Conclusion: 8K cannot afford a default full-frame float Lab/XYZ working buffer
for every surface. Keep the presentation and common UI hot path as packed
premultiplied 32-bit color. Use Lab/XYZ as explicit color values, asset profile
metadata, conversion working space, and tile-local intermediate state.

## Recommended Local Architecture

1. Add a pure Simple color module:
   - `src/lib/common/color/color_space.spl`
   - `src/lib/common/color/cie_xyz.spl`
   - `src/lib/common/color/cielab.spl`
   - `src/lib/common/color/color_convert.spl`

2. Keep framebuffer format separate from color math:
   - hot render target: premultiplied `argb8888` or `rgba8888`;
   - semantic color value default: CIELAB with explicit white point;
   - connection color space: CIE XYZ D50/D65;
   - conversion output: target surface profile and packed framebuffer.

3. Do not switch the whole lib set at startup. Use a per-surface or per-asset
   `ColorPipelinePolicy` with lazy initialization:
   - default fast path: sRGB/argb8888 direct;
   - Lab/XYZ path: initialized only if CSS/image/theme requests it;
   - codec path: decoder initialized only if TIFF/JXL assets are encountered;
   - GPU/SIMD conversion kernels: initialized on first use and cached.

4. Integrate image codecs through a shared image facade:
   - `ImageInfo`: dimensions, pixel format, color profile, orientation, alpha;
   - `ImageDecodeOptions`: desired output format, desired output color space,
     tile size, strict metadata mode;
   - `ImageFrame`: packed output buffer plus optional retained source profile.

5. Put TIFF/JXL pure Simple support behind staged decode milestones:
   - TIFF baseline: endian parser, IFDs, strips, uncompressed RGB/gray/Lab,
     PackBits, LZW/Deflate later, tiled TIFF later.
   - JPEG XL baseline: container/codestream parser and metadata first; pure
     Simple full image decode is large and should be staged with conformance
     fixtures. Web rendering can initially gate JXL support to metadata plus
     fail-closed unsupported codestream subsets until decoder milestones pass.

## Risks

- A global startup color-mode switch would add cold-start delay and increase RSS
  even for pages that use only sRGB and packed bitmap assets.
- Converting every frame through Lab/XYZ would break the current exact-pixel and
  performance lanes. Lab/XYZ conversion must be tile-local and demand-driven.
- TIFF and JPEG XL security surfaces are parser-heavy. Add bounds checks,
  allocation caps, and fuzz/conformance fixtures before enabling broad browser
  decode.

