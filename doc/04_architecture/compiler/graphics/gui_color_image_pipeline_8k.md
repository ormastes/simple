# GUI Color/Image Pipeline 8K Architecture

Date: 2026-06-01

Selected requirement option: Option A, lazy color/image pipeline with a packed 8K framebuffer.

## Architecture

The 8K GUI color/image lane keeps the default render target as packed 32-bit pixels and moves wide-color or codec work behind asset-local gates. A 7680x4320 BGRA8 surface is planned as 132,710,400 framebuffer bytes. Full-frame Lab/XYZ buffers are not allocated during surface planning.

`src/lib/common/color/lab_xyz.spl` owns the semantic color model and packed 8K surface policy. CIELAB is the semantic color API for perceptual operations; CIE XYZ is the explicit conversion/profile connection space. Browser GPU surface planning consumes that policy through `examples/11_advanced/browser/feature/gpu/surface.spl`.

`src/lib/common/image/image_info.spl` owns lightweight image metadata and color-profile routing. It detects TIFF, JPEG XL, PNG iCCP, JPEG APP2 ICC, and TIFF ICC metadata without initializing decoders or transform caches. Unsupported profile subsets fail closed with typed reasons. RGB/XYZ ICC profiles may use the current packed-sRGB identity path; RGB/Lab ICC profiles are not treated as identity and return `icc-rgb-lab-transform-pending`.

`examples/11_advanced/browser/feature/paint/image_decode.spl` owns staged pure-Simple decode integration. TIFF has exact RGBA capability slices for current supported variants. JPEG XL currently provides metadata, container/codestream parsing, split partial codestream stitching, color metadata routing, and sparse intrinsic-size placeholders; full Modular or VarDCT pixel decode remains outside the current accepted claim.

## Boundaries

- Hot path: packed BGRA8/ARGB/RGBA framebuffer planning and exact pixel evidence.
- Lazy path: Lab/XYZ conversion, ICC/profile routing, TIFF decode, JPEG XL metadata and future pixel decode.
- Fail-closed path: compressed PNG ICC transforms, non-identity RGB/Lab ICC, unsupported TIFF/JPEG XL subsets, malformed containers, and oversized metadata-only images that should stay sparse.

## Evidence

The authoritative gate is `scripts/check/check-gui-color-image-pipeline-8k-evidence.shs`. It runs the generated 8K surface/color probe plus focused surface, Lab/XYZ, image decode, and TIFF raster specs.
