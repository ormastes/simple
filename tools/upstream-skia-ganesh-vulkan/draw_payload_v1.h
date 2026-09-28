#ifndef SIMPLE_UPSTREAM_SKIA_DRAW_PAYLOAD_V1_H
#define SIMPLE_UPSTREAM_SKIA_DRAW_PAYLOAD_V1_H

#include <stdint.h>
#include <stddef.h>

/* Private wire format for the opt-in authenticated GPU provider. All fields
 * are native little-endian, copied during submit(), and never stored as a
 * borrowed DrawIrComposition pointer. Only filled source-over rectangles are
 * admitted in v1. The Simple adapter preflights the entire composition first.
 */
#define SIMPLE_UPSTREAM_SKIA_DRAW_MAGIC_V1 UINT32_C(0x314b5355)
#define SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V1 UINT32_C(0x31564b53)
#define SIMPLE_UPSTREAM_SKIA_MAX_RECTS_V1 UINT32_C(65536)
#define SIMPLE_UPSTREAM_SKIA_DRAW_MAGIC_V2 UINT32_C(0x324b5355)
#define SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V2 UINT32_C(0x32564b53)
#define SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT UINT32_C(1)
#define SIMPLE_UPSTREAM_SKIA_DRAW_MAGIC_V3 UINT32_C(0x334b5355)
#define SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V3 UINT32_C(0x33564b53)
#define SIMPLE_UPSTREAM_SKIA_RECT_V3_AFFINE_PRESENT UINT32_C(2)
#define SIMPLE_UPSTREAM_SKIA_RASTER_ALIASED_V3 UINT32_C(0)
#define SIMPLE_UPSTREAM_SKIA_RASTER_COVERAGE_AA_V3 UINT32_C(1)

typedef struct SimpleUpstreamSkiaDrawHeaderV1 {
    uint32_t magic;
    uint32_t width;
    uint32_t height;
    uint32_t rect_count;
} SimpleUpstreamSkiaDrawHeaderV1;

typedef struct SimpleUpstreamSkiaRectV1 {
    double x;
    double y;
    double width;
    double height;
    uint32_t argb;
    uint32_t reserved;
} SimpleUpstreamSkiaRectV1;

/* V2 keeps the same header shape and extends each rectangle with an optional
 * target-coordinate clip. The first full-target clear must have flags == 0.
 * Each clip is scoped to its rectangle; it cannot leak into the next draw.
 */
typedef struct SimpleUpstreamSkiaRectV2 {
    double x;
    double y;
    double width;
    double height;
    uint32_t argb;
    uint32_t reserved;
    int32_t clip_x;
    int32_t clip_y;
    int32_t clip_width;
    int32_t clip_height;
    uint32_t flags;
    uint32_t reserved2;
} SimpleUpstreamSkiaRectV2;

/* V3 appends local-to-surface affine state to the immutable v2 prefix. When
 * AFFINE_PRESENT is clear, all six coefficients must be zero. A present clip
 * remains in surface coordinates, so future execution must apply it before
 * concatenating the affine transform. The first full-target clear carries no
 * clip, affine state, or coverage AA. No v3 bytes are emitted/admitted yet.
 */
typedef struct SimpleUpstreamSkiaRectV3 {
    double x;
    double y;
    double width;
    double height;
    uint32_t argb;
    uint32_t reserved;
    int32_t clip_x;
    int32_t clip_y;
    int32_t clip_width;
    int32_t clip_height;
    uint32_t flags;
    uint32_t reserved2;
    double affine_a;
    double affine_b;
    double affine_c;
    double affine_d;
    double affine_tx;
    double affine_ty;
    uint32_t raster_policy;
    uint32_t reserved3;
    uint64_t reserved4;
} SimpleUpstreamSkiaRectV3;

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
_Static_assert(sizeof(SimpleUpstreamSkiaDrawHeaderV1) == 16, "draw header ABI drift");
_Static_assert(sizeof(SimpleUpstreamSkiaRectV1) == 40, "draw rect ABI drift");
_Static_assert(sizeof(SimpleUpstreamSkiaRectV2) == 64, "draw rect v2 ABI drift");
_Static_assert(offsetof(SimpleUpstreamSkiaRectV2, clip_x) == 40, "draw clip offset drift");
_Static_assert(offsetof(SimpleUpstreamSkiaRectV2, flags) == 56, "draw flags offset drift");
_Static_assert(sizeof(SimpleUpstreamSkiaRectV3) == 128, "draw rect v3 ABI drift");
_Static_assert(offsetof(SimpleUpstreamSkiaRectV3, clip_x) == 40, "draw v3 clip offset drift");
_Static_assert(offsetof(SimpleUpstreamSkiaRectV3, flags) == 56, "draw v3 flags offset drift");
_Static_assert(offsetof(SimpleUpstreamSkiaRectV3, affine_a) == 64, "draw v3 affine offset drift");
_Static_assert(offsetof(SimpleUpstreamSkiaRectV3, raster_policy) == 112, "draw v3 raster offset drift");
_Static_assert(offsetof(SimpleUpstreamSkiaRectV3, reserved4) == 120, "draw v3 reserved offset drift");
#endif

#if defined(__cplusplus)
static_assert(sizeof(SimpleUpstreamSkiaDrawHeaderV1) == 16, "draw header ABI drift");
static_assert(sizeof(SimpleUpstreamSkiaRectV1) == 40, "draw rect v1 ABI drift");
static_assert(sizeof(SimpleUpstreamSkiaRectV2) == 64, "draw rect v2 ABI drift");
static_assert(sizeof(SimpleUpstreamSkiaRectV3) == 128, "draw rect v3 ABI drift");
static_assert(offsetof(SimpleUpstreamSkiaRectV3, clip_x) == 40, "draw v3 clip offset drift");
static_assert(offsetof(SimpleUpstreamSkiaRectV3, flags) == 56, "draw v3 flags offset drift");
static_assert(offsetof(SimpleUpstreamSkiaRectV3, affine_a) == 64, "draw v3 affine offset drift");
static_assert(offsetof(SimpleUpstreamSkiaRectV3, raster_policy) == 112, "draw v3 raster offset drift");
static_assert(offsetof(SimpleUpstreamSkiaRectV3, reserved4) == 120, "draw v3 reserved offset drift");
#endif

#endif
