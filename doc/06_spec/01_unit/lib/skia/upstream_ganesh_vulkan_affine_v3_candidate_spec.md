# Upstream Ganesh Vulkan affine V3 candidate specification

Source: `test/01_unit/lib/skia/upstream_ganesh_vulkan_affine_v3_candidate_spec.spl`

Status: **written, not executed**. The Simple verifier cap prevents a runtime
run in this session. The pinned Skia checkout and physical Vulkan capture are
also absent. This manual records expected behavior, not a PASS result.

## Admission boundary

The explicit `upstream_skia_ganesh_vulkan_preflight_affine_v3_candidate`
entrypoint accepts only a Draw IR V4, one GPU offscreen batch, an opaque
integer full-target first clear, and later plain opaque rectangles. Later
rectangles may carry a local f64 affine transform and coverage AA policy.
Per-command clips must be positive, exactly representable target-space
rectangles within the surface. Hidden text/image/path payload, computed
style, parent, border/content/hit metadata, unsupported geometry, and
non-opaque paint reject the entire composition before provider work.

The native wire validator's float model is mirrored in Simple: the submitted
f32 matrix must remain finite and invertible, and conservative transformed
corner error may not exceed 0.125 pixel on either axis. A scene that becomes
singular after f32 rounding or exceeds the error budget is rejected at the
offending command index.

## V3 wire

`upstream_skia_ganesh_vulkan_payload_bytes_affine_v3_candidate` uses the
same serializer as the candidate render path. The 16-byte header has V3 magic
`0x334b5355`; every record is 128 bytes. The immutable V1 and V2 record
layouts and default render path are unchanged. A V3 record contains the
V2 geometry, color, clip, and flags prefix; six f64 affine coefficients at
offsets 64–111; raster policy at 112; and zero reserved words. Clip and
affine flags are 1 and 2, respectively. Coverage AA is raster policy 1.
Absent clip or affine fields are fully zeroed, including the first clear.

## Scenarios

1. A full clear followed by a clipped, translated, coverage-AA local rectangle
   selects format `0x33564b53`, magic `0x334b5355`, stride 128, and two records.
   The ordinary V1/V2 preflight and render remain closed for this composition.
2. The candidate serializer emits 272 bytes for that scene and places the V3
   magic, clip-plus-affine flags, coefficient bits, raster policy, and reserved
   zeros at the specified offsets.
3. A matrix invertible in f64 but singular after f32 rounding, and a matrix
   whose guarded corner error exceeds 0.125 pixel, are rejected.
4. An affine first draw or hidden parent metadata rejects the whole scene.

Candidate admission and bytes do not mean native V3 execution is enabled.
The provider's native V3 build flag remains default-disabled. Physical
device pixels, antialias coverage, and cross-backend tolerance require
separate qualified evidence.
