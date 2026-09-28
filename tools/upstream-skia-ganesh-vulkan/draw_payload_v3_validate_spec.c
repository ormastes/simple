/* Focused native CPU contract check for REQ-2D-005 / NFR-2D-005.
 * The v3 renderer remains disabled even when shape validation succeeds.
 */
#include "draw_payload_v3_validate.h"
#include <string.h>

int main(void) {
    SimpleUpstreamSkiaDrawHeaderV1 header = {
        SIMPLE_UPSTREAM_SKIA_DRAW_MAGIC_V3, 16, 16, 2
    };
    SimpleUpstreamSkiaRectV3 clear = {0};
    clear.width = 16.0;
    clear.height = 16.0;
    clear.argb = UINT32_C(0xff000000);
    SimpleUpstreamSkiaRectV3 draw = {0};
    draw.x = 1.0;
    draw.y = 1.0;
    draw.width = 4.0;
    draw.height = 4.0;
    draw.argb = UINT32_C(0xff336699);
    draw.clip_x = 14;
    draw.clip_y = 0;
    draw.clip_width = 2;
    draw.clip_height = 2;
    draw.flags = SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT;
    uint8_t payload[sizeof(header) + 2 * sizeof(draw)];
    memcpy(payload, &header, sizeof(header));
    memcpy(payload + sizeof(header), &clear, sizeof(clear));
    memcpy(payload + sizeof(header) + sizeof(clear), &draw, sizeof(draw));
    double corner_error = 0.0;
    if (!simple_upstream_skia_v3_payload_valid(
            payload, sizeof(payload), 16, 16, &corner_error)) return 1;
    draw.clip_x = 15; /* Right edge 17 exceeds the 16-pixel target. */
    memcpy(payload + sizeof(header) + sizeof(clear), &draw, sizeof(draw));
    if (simple_upstream_skia_v3_payload_valid(
            payload, sizeof(payload), 16, 16, &corner_error)) return 2;
    draw.clip_x = 14;
    draw.width = DBL_MAX;
    memcpy(payload + sizeof(header) + sizeof(clear), &draw, sizeof(draw));
    if (simple_upstream_skia_v3_payload_valid(
            payload, sizeof(payload), 16, 16, &corner_error)) return 3;
    draw.width = 4.0;
    draw.x = 0.0;
    draw.y = 0.0;
    draw.flags |= SIMPLE_UPSTREAM_SKIA_RECT_V3_AFFINE_PRESENT;
    draw.affine_a = DBL_MAX;
    draw.affine_d = 1.0;
    memcpy(payload + sizeof(header) + sizeof(clear), &draw, sizeof(draw));
    if (simple_upstream_skia_v3_payload_valid(
            payload, sizeof(payload), 16, 16, &corner_error)) return 4;
    return 0;
}
