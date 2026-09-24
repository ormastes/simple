#ifndef SIMPLE_UPSTREAM_SKIA_DRAW_PAYLOAD_V3_VALIDATE_H
#define SIMPLE_UPSTREAM_SKIA_DRAW_PAYLOAD_V3_VALIDATE_H

#include "draw_payload_v1.h"
#include <float.h>
#include <string.h>

/* CPU-only v3 shape preflight. It is deliberately independent of Skia headers,
 * so the private wire can be checked before a pinned Ganesh build exists.
 * Passing this function does not enable execution: submit() still rejects v3.
 */
static inline int simple_skia_v3_finite(double value) {
    return value == value && value >= -DBL_MAX && value <= DBL_MAX;
}

static inline double simple_skia_v3_abs(double value) {
    return value < 0.0 ? -value : value;
}

static inline int simple_skia_v3_scalar_range(double value) {
    return simple_skia_v3_finite(value) &&
           value >= -FLT_MAX && value <= FLT_MAX;
}

static inline int simple_skia_v3_exact_scalar(double value) {
    if (!simple_skia_v3_scalar_range(value)) return 0;
    const float scalar = (float)value;
    return (double)scalar == value;
}

static inline int simple_skia_v3_zero_affine(const SimpleUpstreamSkiaRectV3 *rect) {
    return rect->affine_a == 0.0 && rect->affine_b == 0.0 &&
           rect->affine_c == 0.0 && rect->affine_d == 0.0 &&
           rect->affine_tx == 0.0 && rect->affine_ty == 0.0;
}

static inline int simple_skia_v3_corner_error(const SimpleUpstreamSkiaRectV3 *rect,
                                                double *maximum) {
    const double original[6] = {rect->affine_a, rect->affine_b,
        rect->affine_c, rect->affine_d, rect->affine_tx, rect->affine_ty};
    float submitted[6];
    for (int i = 0; i < 6; ++i) {
        if (!simple_skia_v3_scalar_range(original[i])) return 0;
        submitted[i] = (float)original[i];
    }
    const float determinant = submitted[0] * submitted[3] -
                              submitted[1] * submitted[2];
    if (determinant != determinant || determinant < -FLT_MAX ||
        determinant > FLT_MAX || determinant == 0.0f) return 0;
    if (!simple_skia_v3_scalar_range(rect->x) ||
        !simple_skia_v3_scalar_range(rect->y) ||
        !simple_skia_v3_scalar_range(rect->width) ||
        !simple_skia_v3_scalar_range(rect->height)) return 0;
    const float fx = (float)rect->x;
    const float fy = (float)rect->y;
    const float fw = (float)rect->width;
    const float fh = (float)rect->height;
    if (fw <= 0.0f || fh <= 0.0f) return 0;
    const float right = fx + fw;
    const float bottom = fy + fh;
    if (right < -FLT_MAX || right > FLT_MAX ||
        bottom < -FLT_MAX || bottom > FLT_MAX) return 0;
    const double ox[4] = {rect->x, rect->x + rect->width,
        rect->x, rect->x + rect->width};
    const double oy[4] = {rect->y, rect->y,
        rect->y + rect->height, rect->y + rect->height};
    const double qx[4] = {(double)fx, (double)right,
        (double)fx, (double)right};
    const double qy[4] = {(double)fy, (double)fy,
        (double)bottom, (double)bottom};
    double worst = 0.0;
    for (int i = 0; i < 4; ++i) {
        const double source_x = original[0] * ox[i] + original[2] * oy[i] + original[4];
        const double source_y = original[1] * ox[i] + original[3] * oy[i] + original[5];
        const double mapped_x = (double)submitted[0] * qx[i] +
            (double)submitted[2] * qy[i] + (double)submitted[4];
        const double mapped_y = (double)submitted[1] * qx[i] +
            (double)submitted[3] * qy[i] + (double)submitted[5];
        if (!simple_skia_v3_finite(source_x) || !simple_skia_v3_finite(source_y) ||
            !simple_skia_v3_finite(mapped_x) || !simple_skia_v3_finite(mapped_y))
            return 0;
        const double guard_x = 8.0 * FLT_EPSILON *
            (simple_skia_v3_abs(mapped_x) +
             simple_skia_v3_abs((double)submitted[0] * qx[i]) +
             simple_skia_v3_abs((double)submitted[2] * qy[i]) +
             simple_skia_v3_abs((double)submitted[4]) + 1.0);
        const double guard_y = 8.0 * FLT_EPSILON *
            (simple_skia_v3_abs(mapped_y) +
             simple_skia_v3_abs((double)submitted[1] * qx[i]) +
             simple_skia_v3_abs((double)submitted[3] * qy[i]) +
             simple_skia_v3_abs((double)submitted[5]) + 1.0);
        const double error_x = simple_skia_v3_abs(source_x - mapped_x) + guard_x;
        const double error_y = simple_skia_v3_abs(source_y - mapped_y) + guard_y;
        if (!simple_skia_v3_finite(error_x) || !simple_skia_v3_finite(error_y) ||
            error_x > 0.125 || error_y > 0.125) return 0;
        if (error_x > worst) worst = error_x;
        if (error_y > worst) worst = error_y;
    }
    *maximum = worst;
    return 1;
}

static inline int simple_upstream_skia_v3_payload_valid(
    const uint8_t *data, uint64_t length, uint32_t target_width,
    uint32_t target_height, double *max_corner_error) {
    if (!data || !max_corner_error || length < sizeof(SimpleUpstreamSkiaDrawHeaderV1))
        return 0;
    SimpleUpstreamSkiaDrawHeaderV1 header;
    memcpy(&header, data, sizeof(header));
    if (header.magic != SIMPLE_UPSTREAM_SKIA_DRAW_MAGIC_V3 ||
        header.width != target_width || header.height != target_height ||
        !header.rect_count || header.rect_count > SIMPLE_UPSTREAM_SKIA_MAX_RECTS_V1 ||
        length != sizeof(header) +
            (uint64_t)header.rect_count * sizeof(SimpleUpstreamSkiaRectV3))
        return 0;
    double worst = 0.0;
    for (uint32_t i = 0; i < header.rect_count; ++i) {
        SimpleUpstreamSkiaRectV3 rect;
        memcpy(&rect, data + sizeof(header) +
            (uint64_t)i * sizeof(rect), sizeof(rect));
        if (rect.reserved || rect.reserved2 || rect.reserved3 || rect.reserved4 ||
            (rect.argb >> 24) != 0xff ||
            (rect.flags & ~(SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT |
                            SIMPLE_UPSTREAM_SKIA_RECT_V3_AFFINE_PRESENT)) ||
            rect.raster_policy > SIMPLE_UPSTREAM_SKIA_RASTER_COVERAGE_AA_V3 ||
            !simple_skia_v3_finite(rect.x) || !simple_skia_v3_finite(rect.y) ||
            !simple_skia_v3_finite(rect.width) ||
            !simple_skia_v3_finite(rect.height) ||
            rect.width <= 0.0 || rect.height <= 0.0)
            return 0;
        if (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT) {
            const int64_t right = (int64_t)rect.clip_x + rect.clip_width;
            const int64_t bottom = (int64_t)rect.clip_y + rect.clip_height;
            if (i == 0 || rect.clip_x < 0 || rect.clip_y < 0 ||
                rect.clip_width <= 0 || rect.clip_height <= 0 ||
                right > (int64_t)header.width ||
                bottom > (int64_t)header.height ||
                !simple_skia_v3_exact_scalar((double)rect.clip_x) ||
                !simple_skia_v3_exact_scalar((double)rect.clip_y) ||
                !simple_skia_v3_exact_scalar((double)rect.clip_width) ||
                !simple_skia_v3_exact_scalar((double)rect.clip_height) ||
                !simple_skia_v3_exact_scalar((double)right) ||
                !simple_skia_v3_exact_scalar((double)bottom)) return 0;
        } else if (rect.clip_x || rect.clip_y || rect.clip_width || rect.clip_height) {
            return 0;
        }
        if (i == 0) {
            if (rect.flags || rect.raster_policy || !simple_skia_v3_zero_affine(&rect) ||
                rect.x != 0.0 || rect.y != 0.0 ||
                rect.width != (double)header.width ||
                rect.height != (double)header.height) return 0;
        }
        if (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V3_AFFINE_PRESENT) {
            double error = 0.0;
            if (i == 0 || rect.x != 0.0 || rect.y != 0.0 ||
                !simple_skia_v3_corner_error(&rect, &error)) return 0;
            if (error > worst) worst = error;
        } else {
            if (!simple_skia_v3_zero_affine(&rect) ||
                !simple_skia_v3_exact_scalar(rect.x) ||
                !simple_skia_v3_exact_scalar(rect.y) ||
                !simple_skia_v3_exact_scalar(rect.width) ||
                !simple_skia_v3_exact_scalar(rect.height) ||
                (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT ?
                    !simple_skia_v3_exact_scalar(rect.x + rect.width) ||
                    !simple_skia_v3_exact_scalar(rect.y + rect.height) :
                    rect.x < 0.0 || rect.y < 0.0 ||
                    rect.x + rect.width > header.width ||
                    rect.y + rect.height > header.height)) return 0;
        }
    }
    *max_corner_error = worst;
    return 1;
}

#endif
