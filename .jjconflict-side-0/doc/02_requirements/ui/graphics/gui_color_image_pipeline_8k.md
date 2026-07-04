# GUI Color/Image Pipeline 8K Requirements

Date: 2026-06-01

Selected option: Option A, lazy color/image pipeline with packed 8K framebuffer.

## Requirements

- REQ-GCI8K-001: Default 8K GUI, browser, and web render surfaces must keep the hot render target in packed 32-bit ARGB/RGBA/BGRA form, with a 7680x4320 framebuffer reported as 132,710,400 bytes.
- REQ-GCI8K-002: CIELAB must be the default semantic color API for perceptual color operations, while CIE XYZ remains the explicit profile/conversion connection space.
- REQ-GCI8K-003: Lab/XYZ transforms, ICC/profile parsing, TIFF decoding, and JPEG XL decoding must initialize lazily per surface or asset, not during default startup or 8K surface planning.
- REQ-GCI8K-004: Browser GPU surface planning must identify which formats are eligible for the packed 8K hot path and reject non-32-bit formats such as RGB565 from that path.
- REQ-GCI8K-005: Pure Simple TIFF support must continue through explicit capability slices with exact RGBA evidence for endian parsing, strips, tiles, PackBits, planar data, palette data, high-bit-depth samples, grayscale, RGB/RGBA, and Lab-like paths.
- REQ-GCI8K-006: Pure Simple JPEG XL support must stage metadata, container/codestream color parsing, sparse 8K allocation policy, and bounded pixel decode subsets before any claim of full image decode.
- REQ-GCI8K-007: Web rendering and Simple browser image paths must consume shared color/image metadata and raster facades so TIFF/JPEG XL/color-profile behavior is not duplicated per frontend.
- REQ-GCI8K-008: Unsupported color/profile/codec subsets must fail closed with typed diagnostics rather than silently rendering approximate pixels.
- REQ-GCI8K-009: Every accepted image/color rendering milestone must have exact RGBA or packed-pixel checksum evidence and must not use blur, perceptual, or tolerance-based screenshot acceptance.

## Deleted Options

Options B and C from the options document are not selected. Do not preserve global always-on CIELAB full-frame rendering or codec-only-without-color-pipeline as accepted requirements.
