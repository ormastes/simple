/* Include the exact cold leaf to exercise its bounded note parser as well as
 * its actual exported main-image snapshot. Target is a separate XRay object. */
#include "../../../src/runtime/xray/xray_llvm_image_linux.c"
#include <stdio.h>
extern int locator_target(int);
#ifndef LOCATOR_ABSENT_SECTION
__attribute__((section("simple_xray_semantic_v1"), used))
unsigned char locator_rows[24] = {1, 2, 3, 4};
#endif
#define CHECK(x) do { if (!(x)) { fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #x); return 1; } ++checks; } while (0)
int main(void) {
    int checks = 0;
    CHECK(locator_target(8) == 15);
    CHECK(simple_xray_image_snapshot_word_v1(1, 0) == -1);
#ifdef LOCATOR_ABSENT_SECTION
    CHECK(simple_xray_image_snapshot_create_v1(1048576, 65536) == SIMPLE_XRAY_IMAGE_ABSENT_V1);
#else
    CHECK(simple_xray_image_snapshot_create_v1(1, 65536) == SIMPLE_XRAY_IMAGE_EXHAUSTED_V1);
    CHECK(simple_xray_image_snapshot_word_v1(1, 0) == -1);
    int64_t h = simple_xray_image_snapshot_create_v1(1048576, 65536);
    CHECK(h == 1);
    CHECK(simple_xray_image_snapshot_word_v1(h, 0) == 1);
    CHECK(simple_xray_image_snapshot_word_v1(h, 1) == (int64_t)(uintptr_t)locator_rows);
    CHECK(simple_xray_image_snapshot_word_v1(h, 2) == sizeof(locator_rows));
    CHECK(simple_xray_image_snapshot_word_v1(h, 5) == 20);
    int64_t bytes = simple_xray_image_snapshot_word_v1(h, 6);
    int64_t count = simple_xray_image_snapshot_word_v1(h, 4);
    CHECK(bytes > (int64_t)sizeof(struct image_snapshot));
    CHECK(count > 0);
    CHECK(simple_xray_image_snapshot_create_v1(bytes - 1, 65536) == SIMPLE_XRAY_IMAGE_EXHAUSTED_V1);
    CHECK(simple_xray_image_snapshot_create_v1(bytes, count - 1) == SIMPLE_XRAY_IMAGE_EXHAUSTED_V1);
    CHECK(simple_xray_image_snapshot_create_v1(bytes, count) == h);
    int found = 0;
    for (int64_t i = 0; i < count; ++i) {
        int64_t id = simple_xray_image_snapshot_function_word_v1(h, i, 0);
        int64_t address = simple_xray_image_snapshot_function_word_v1(h, i, 1);
        CHECK(id == i + 1);
        CHECK(address == (int64_t)__xray_function_address((int32_t)id));
        if (address == (int64_t)(uintptr_t)locator_target) found = 1;
    }
    CHECK(found);
    locator_rows[0] = 99;
    CHECK(simple_xray_image_snapshot_section_byte_v1(h, 0) == 1);
    CHECK(simple_xray_image_snapshot_section_byte_v1(h, -1) == -1);
    CHECK(simple_xray_image_snapshot_section_byte_v1(h, 24) == -1);
    CHECK(simple_xray_image_snapshot_word_v1(2, 0) == -1);
    CHECK(simple_xray_image_snapshot_word_v1(h, 7) == -1);
    CHECK(simple_xray_image_snapshot_build_id_byte_v1(h, 20) == -1);
    CHECK(simple_xray_image_snapshot_range_word_v1(h, -1, 0) == -1);
    CHECK(simple_xray_image_snapshot_range_word_v1(h, simple_xray_image_snapshot_word_v1(h, 3), 0) == -1);
    CHECK(simple_xray_image_snapshot_function_word_v1(h, count, 0) == -1);
    CHECK(simple_xray_image_snapshot_function_word_v1(h, 0, 2) == -1);
    /* Checked parser edges use owned local memory, never invalid dereferences. */
    unsigned char note[36] = {0};
    Elf64_Nhdr header = {4, 20, NT_GNU_BUILD_ID};
    memcpy(note, &header, sizeof(header)); memcpy(note + 12, "GNU\0", 4);
    memset(note + 16, 17, 20);
    struct image_scan scan = {0};
    scan.count = 1;
    scan.ranges[0] = (struct image_range){(uintptr_t)note, sizeof(note), 1};
    CHECK(read_notes(&scan, (uintptr_t)note, sizeof(note)) == 1);
    CHECK(scan.has_build_id && scan.build_id[0] == 17);
    note[16] = 18;
    CHECK(read_notes(&scan, (uintptr_t)note, sizeof(note)) == 0);
    CHECK(read_notes(&scan, (uintptr_t)note, 11) == 0);
    CHECK(read_notes(&scan, (uintptr_t)note, sizeof(note) + 1) == 0);
    header.n_descsz = UINT32_MAX; memcpy(note, &header, sizeof(header));
    CHECK(read_notes(&scan, (uintptr_t)note, sizeof(note)) == 0);
#endif
    printf("PASS Linux XRay image locator: %d checks\n", checks);
    return 0;
}
