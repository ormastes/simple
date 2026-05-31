# GUI Color/Image Pipeline 8K Agent Tasks

Date: 2026-05-31

## Objective

Extend GUI hardening to target 8K 32-bit full-color rendering with CIELAB
default semantic color support, CIE XYZ conversion support, and pure Simple TIFF
and JPEG XL image support in Simple web rendering and Simple browser.

## Task Breakdown

1. Color model foundation
   - Add CIELAB, CIE XYZ D50/D65, packed ARGB/RGBA, and color profile metadata
     types under `src/lib/common/color/`.
   - Add exact conversion tests using published sample values and round-trip
     tolerances only for numeric color conversion, not screenshot acceptance.

2. 8K framebuffer policy
   - Add render-surface policy documenting packed 32-bit default buffers.
   - Add a test that proves default 8K planning does not allocate full-frame
     Lab/XYZ float intermediates.

3. Image facade
   - Add common image info/decode options/frame structures.
   - Thread image metadata through `web_render_api`, Simple browser image load,
     and WM image surface paths.

4. TIFF pure Simple milestone
   - Implement endian header, IFD parsing, bounds checks, uncompressed strips,
     gray/RGB/Lab baseline, then PackBits.
   - Add fail-closed unsupported compression and allocation-cap tests.

5. JPEG XL pure Simple milestone
   - Implement container/codestream signature and metadata parsing first.
   - Add staged decoder tasks with official conformance fixtures before claiming
     full image decode.
   - Keep unsupported codestream features fail-closed in web/browser rendering.

6. Lazy initialization and perf evidence
   - Instrument codec/color transform first-use time, steady-state tile cost,
     cache hits, RSS delta, and 8K frame timings.
   - Prove startup does not initialize TIFF/JXL/color transforms unless needed.

## Current Recommendation

Adopt lazy per-surface/per-asset policy rather than whole-library startup
switching. Keep 8K display buffers packed and perform Lab/XYZ work in tile-local
conversion stages.

