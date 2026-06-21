# GUI Color/Image Pipeline 8K Design

Date: 2026-06-01

## Requirement Mapping

- REQ-GCI8K-001 and NFR-GCI8K-001: `plan_packed_8k_surface` and browser surface planning report 7680x4320x4 as 132,710,400 bytes.
- REQ-GCI8K-002: `lab_xyz.spl` exposes CIELAB semantic helpers and CIE XYZ conversion helpers.
- REQ-GCI8K-003 and NFR-GCI8K-003: surface plans record `initializes_color_transforms=false`, `initializes_tiff_decoder=false`, and `initializes_jpegxl_decoder=false`.
- REQ-GCI8K-004: `surface_matches_packed_color_plan` rejects non-32-bit formats such as RGB565 from the packed 8K hot path.
- REQ-GCI8K-005: `decode_tiff` and `tiff_image_raster_spec.spl` cover endian, strip, tile, PackBits, planar, palette, gray, RGB/RGBA, high-bit-depth, and Lab-like slices.
- REQ-GCI8K-006: `jpeg_xl_image_info` covers staged codestream/container metadata, split partial codestream stitching, 8K intrinsic dimensions, and color metadata routing without claiming full pixel decode.
- REQ-GCI8K-007: browser decode paths use shared `std.common.image.image_info` metadata and shared color helpers.
- REQ-GCI8K-008 and NFR-GCI8K-007: unsupported color/profile/codec paths return typed reasons such as `compressed-icc-transform-pending`, `icc-rgb-lab-transform-pending`, and JPEG XL malformed-container diagnostics.
- REQ-GCI8K-009 and NFR-GCI8K-006: accepted raster milestones use exact RGBA arrays, packed values, checksums, or mismatch-free evidence; no blur/tolerance acceptance is used.

## Current Bounded Slice

The non-identity ICC slice separates RGB/XYZ ICC profiles from RGB/Lab ICC profiles. RGB/XYZ remains a supported identity packed-sRGB path. RGB/Lab is now explicitly unsupported until a real profile transform exists, so browser/image rendering cannot silently accept non-identity profile pixels.

## Follow-Up Design Work

- Add real ICC tag-table/TRC/matrix processing before supporting non-identity RGB/Lab or RGB/XYZ transforms.
- Add JPEG XL Modular pixel decode slices before claiming rendered JXL pixels.
- Add first-use timing/RSS/tile-count diagnostics for each lazy codec and profile stage.
