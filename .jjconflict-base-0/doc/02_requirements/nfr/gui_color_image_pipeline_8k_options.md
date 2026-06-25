<!-- codex-research -->
# GUI Color/Image Pipeline 8K NFR Options

Date: 2026-05-31

## Option A: 8K Packed Hot Path, Lazy Wide-Color Work

Description: 8K rendering defaults to packed 32-bit full-color buffers. CIELAB,
XYZ, ICC/profile conversion, TIFF, and JPEG XL work is demand-driven and
tile-local. Startup must not initialize unused codec/color backends.

Pros:
- Bounded startup time and memory.
- Keeps exact-pixel gates meaningful.
- Allows SIMD/GPU conversion kernels without forcing them into every frame.

Cons:
- Requires policy and cache instrumentation.
- Requires tests proving transforms are not initialized unnecessarily.

Effort: L. Expected 10-18 verification and instrumentation files.

Targets:
- 8K single framebuffer memory remains about 126.6 MiB for 32-bit color.
- No full-frame Lab/XYZ float buffer allocation in default sRGB pages.
- Startup initializes zero TIFF/JXL decoders unless an asset requires them.
- First-use color transform cache records init time, tile count, and RSS delta.

## Option B: Quality-First Always-On Wide Color

Description: Always initialize wide-color transforms and keep intermediate
surfaces in float Lab/XYZ-compatible storage.

Pros:
- Maximum internal precision.
- Fewer conditional paths.

Cons:
- Startup delay and RSS cost even for simple pages.
- Poor fit for 8K framebuffers and current benchmark targets.

Effort: XL.

## Option C: Minimal Startup With Optional Native Codec Bridges

Description: Keep pure Simple baseline small but allow native libtiff/libjxl
bridges for performance and compatibility.

Pros:
- Faster broad codec coverage.
- Useful comparison baseline.

Cons:
- Does not satisfy pure Simple support by itself.
- Native dependency can hide parser correctness gaps.

Effort: M plus ongoing pure Simple codec work.

## Recommendation

Choose Option A. Native bridges may be diagnostic/perf references only; the
accepted path must include pure Simple codec support for TIFF and JPEG XL.

