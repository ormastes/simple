/* Private cold-path ABI. Provider serializes create; snapshots remain resident. */
#ifndef SIMPLE_XRAY_LLVM_IMAGE_LINUX_H
#define SIMPLE_XRAY_LLVM_IMAGE_LINUX_H
#include <stdint.h>
#define SIMPLE_XRAY_IMAGE_SCHEMA_V1 1
#define SIMPLE_XRAY_IMAGE_ABSENT_V1 (-1)
#define SIMPLE_XRAY_IMAGE_INVALID_V1 (-2)
#define SIMPLE_XRAY_IMAGE_EXHAUSTED_V1 (-3)
#define SIMPLE_XRAY_IMAGE_UNSUPPORTED_V1 (-4)
#define SIMPLE_XRAY_IMAGE_MAX_RANGES_V1 128
#define SIMPLE_XRAY_IMAGE_MAX_FUNCTIONS_V1 65536
#define SIMPLE_XRAY_IMAGE_MAX_SECTION_V1 (8 * 1024 * 1024)
int64_t simple_xray_image_snapshot_create_v1(int64_t, int64_t);
int64_t simple_xray_image_snapshot_word_v1(int64_t, int64_t);
int64_t simple_xray_image_snapshot_section_byte_v1(int64_t, int64_t);
int64_t simple_xray_image_snapshot_build_id_byte_v1(int64_t, int64_t);
int64_t simple_xray_image_snapshot_range_word_v1(int64_t, int64_t, int64_t);
int64_t simple_xray_image_snapshot_function_word_v1(int64_t, int64_t, int64_t);
#endif
