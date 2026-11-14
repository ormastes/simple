/* Cold, opt-in Linux main-image locator. Never part of the callback TU or
 * normal runtime archive. The Simple owner decodes copied semantic rows and
 * binds them to these actual compiler-rt addresses before admitting a session.
 * create is serialized by that owner; no unload/reclamation is supported. */
#define _GNU_SOURCE
#include "xray_llvm_image_linux.h"
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__)) && \
    __SIZEOF_POINTER__ == 8 && __SIZEOF_LONG__ == 8 && \
    __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#include <link.h>
#include <elf.h>
extern const unsigned char __start_simple_xray_semantic_v1[] __attribute__((weak));
extern const unsigned char __stop_simple_xray_semantic_v1[] __attribute__((weak));
extern size_t __xray_max_function_id(void);
extern uintptr_t __xray_function_address(int32_t);
struct image_range { uint64_t address, size, flags; };
struct image_function { uint64_t id, address; };
struct image_snapshot {
    uint64_t address, length, range_count, function_count, allocation;
    unsigned char build_id[20];
    struct image_range ranges[SIMPLE_XRAY_IMAGE_MAX_RANGES_V1];
    /* function table then copied section, in this one checked allocation */
    _Alignas(struct image_function) unsigned char payload[];
};
_Static_assert(offsetof(struct image_snapshot, payload) % _Alignof(struct image_function) == 0,
               "snapshot function table must be aligned");
struct image_scan {
    struct image_range ranges[SIMPLE_XRAY_IMAGE_MAX_RANGES_V1];
    size_t count;
    unsigned char build_id[20];
    int found, status, has_build_id;
};
static struct image_snapshot *resident;
static int add_address(uint64_t a, uint64_t b, uint64_t *out) {
    if (a > INT64_MAX || b > (uint64_t)INT64_MAX - a) return 0;
    *out = a + b; return 1;
}
static int within(const struct image_range *ranges, size_t count,
                  uint64_t address, uint64_t size, uint64_t flags) {
    uint64_t end;
    if (!size || !add_address(address, size, &end)) return 0;
    for (size_t i = 0; i < count; ++i) {
        const struct image_range *r = &ranges[i];
        if ((r->flags & flags) == flags && address >= r->address &&
            end <= r->address + r->size) return 1;
    }
    return 0;
}
static int read_notes(struct image_scan *scan, uint64_t address, uint64_t size) {
    if (!within(scan->ranges, scan->count, address, size, 1)) return 0;
    const unsigned char *bytes = (const unsigned char *)(uintptr_t)address;
    uint64_t at = 0;
    while (at < size) {
        if (size - at < sizeof(Elf64_Nhdr)) return 0;
        Elf64_Nhdr note;
        memcpy(&note, bytes + at, sizeof(note));
        at += sizeof(note);
        uint64_t name_size = ((uint64_t)note.n_namesz + 3) & ~UINT64_C(3);
        uint64_t desc_size = ((uint64_t)note.n_descsz + 3) & ~UINT64_C(3);
        if (name_size > size - at) return 0;
        uint64_t desc_at = at + name_size;
        if (desc_size > size - desc_at) return 0;
        if (note.n_type == NT_GNU_BUILD_ID && note.n_namesz == 4 &&
            memcmp(bytes + at, "GNU\0", 4) == 0) {
            if (note.n_descsz != 20) return 0;
            if (scan->has_build_id && memcmp(scan->build_id, bytes + desc_at, 20)) return 0;
            memcpy(scan->build_id, bytes + desc_at, 20);
            scan->has_build_id = 1;
        }
        at = desc_at + desc_size;
    }
    return 1;
}
static int scan_main(struct dl_phdr_info *info, size_t info_size, void *context) {
    (void)info_size;
    struct image_scan *scan = context;
    /* dl_iterate_phdr identifies the main program by its empty name. */
    if (!info->dlpi_name || info->dlpi_name[0]) return 0;
    scan->found = 1;
    scan->status = SIMPLE_XRAY_IMAGE_INVALID_V1;
    for (size_t i = 0; i < info->dlpi_phnum; ++i) {
        const Elf64_Phdr *p = &info->dlpi_phdr[i];
        if (p->p_type != PT_LOAD || !p->p_memsz) continue;
        if (scan->count == SIMPLE_XRAY_IMAGE_MAX_RANGES_V1) {
            scan->status = SIMPLE_XRAY_IMAGE_EXHAUSTED_V1; return 1;
        }
        uint64_t address, end;
        if (!add_address(info->dlpi_addr, p->p_vaddr, &address) ||
            !add_address(address, p->p_memsz, &end)) return 1;
        uint64_t flags = ((p->p_flags & PF_R) ? 1 : 0) |
                         ((p->p_flags & PF_W) ? 2 : 0) |
                         ((p->p_flags & PF_X) ? 4 : 0);
        scan->ranges[scan->count++] = (struct image_range){address, p->p_memsz, flags};
    }
    for (size_t i = 0; i < info->dlpi_phnum; ++i) {
        const Elf64_Phdr *p = &info->dlpi_phdr[i];
        if (p->p_type != PT_NOTE || !p->p_memsz) continue;
        uint64_t address;
        if (!add_address(info->dlpi_addr, p->p_vaddr, &address) ||
            !read_notes(scan, address, p->p_memsz)) return 1;
    }
    if (scan->count && scan->has_build_id) scan->status = 0;
    return 1;
}
static const struct image_function *functions(const struct image_snapshot *s) {
    return (const struct image_function *)s->payload;
}
int64_t simple_xray_image_snapshot_create_v1(int64_t max_bytes, int64_t max_functions) {
    if (max_bytes <= 0 || max_functions <= 0) return SIMPLE_XRAY_IMAGE_EXHAUSTED_V1;
    if (resident) {
        if (resident->allocation > (uint64_t)max_bytes ||
            resident->function_count > (uint64_t)max_functions) return SIMPLE_XRAY_IMAGE_EXHAUSTED_V1;
        return 1;
    }
    uint64_t start = (uintptr_t)__start_simple_xray_semantic_v1;
    uint64_t stop = (uintptr_t)__stop_simple_xray_semantic_v1;
    if (!start && !stop) return SIMPLE_XRAY_IMAGE_ABSENT_V1;
    if (!start || stop <= start || stop > INT64_MAX) return SIMPLE_XRAY_IMAGE_INVALID_V1;
    uint64_t length = stop - start;
    if (length > SIMPLE_XRAY_IMAGE_MAX_SECTION_V1) return SIMPLE_XRAY_IMAGE_EXHAUSTED_V1;
    struct image_scan scan = {0};
    dl_iterate_phdr(scan_main, &scan);
    if (!scan.found) return SIMPLE_XRAY_IMAGE_UNSUPPORTED_V1;
    if (scan.status) return scan.status;
    if (!within(scan.ranges, scan.count, start, length, 1)) return SIMPLE_XRAY_IMAGE_INVALID_V1;
    size_t count = __xray_max_function_id();
    if (!count) return SIMPLE_XRAY_IMAGE_ABSENT_V1;
    if (count > SIMPLE_XRAY_IMAGE_MAX_FUNCTIONS_V1 || count > (uint64_t)max_functions)
        return SIMPLE_XRAY_IMAGE_EXHAUSTED_V1;
    size_t bytes = sizeof(struct image_snapshot) + count * sizeof(struct image_function);
    if (length > SIZE_MAX - bytes || bytes + length > (uint64_t)max_bytes)
        return SIMPLE_XRAY_IMAGE_EXHAUSTED_V1;
    bytes += (size_t)length;
    struct image_snapshot *s = calloc(1, bytes);
    if (!s) return SIMPLE_XRAY_IMAGE_EXHAUSTED_V1;
    s->address = start; s->length = length; s->range_count = scan.count;
    s->function_count = count; s->allocation = bytes;
    memcpy(s->ranges, scan.ranges, scan.count * sizeof(struct image_range));
    memcpy(s->build_id, scan.build_id, 20);
    struct image_function *table = (struct image_function *)s->payload;
    for (size_t i = 0; i < count; ++i) {
        uint64_t address = __xray_function_address((int32_t)(i + 1));
        /* Holes and DSO addresses are unsupported, never invented bindings. */
        if (!within(scan.ranges, scan.count, address, 1, 4)) {
            free(s); return SIMPLE_XRAY_IMAGE_INVALID_V1;
        }
        table[i] = (struct image_function){i + 1, address};
    }
    memcpy(s->payload + count * sizeof(struct image_function), (const void *)(uintptr_t)start, length);
    resident = s; /* Only publication; earlier failures leave no snapshot. */
    return 1;
}
int64_t simple_xray_image_snapshot_word_v1(int64_t handle, int64_t field) {
    if (handle != 1 || !resident) return -1;
    switch (field) {
    case 0: return SIMPLE_XRAY_IMAGE_SCHEMA_V1;
    case 1: return resident->address;
    case 2: return resident->length;
    case 3: return resident->range_count;
    case 4: return resident->function_count;
    case 5: return 20;
    case 6: return resident->allocation;
    default: return -1;
    }
}
int64_t simple_xray_image_snapshot_section_byte_v1(int64_t handle, int64_t index) {
    if (handle != 1 || !resident || index < 0 || (uint64_t)index >= resident->length) return -1;
    return resident->payload[resident->function_count * sizeof(struct image_function) + index];
}
int64_t simple_xray_image_snapshot_build_id_byte_v1(int64_t handle, int64_t index) {
    if (handle != 1 || !resident || index < 0 || index >= 20) return -1;
    return resident->build_id[index];
}
int64_t simple_xray_image_snapshot_range_word_v1(int64_t handle, int64_t index, int64_t field) {
    if (handle != 1 || !resident || index < 0 || (uint64_t)index >= resident->range_count) return -1;
    const struct image_range *r = &resident->ranges[index];
    switch (field) { case 0: return r->address; case 1: return r->size; case 2: return r->flags; default: return -1; }
}
int64_t simple_xray_image_snapshot_function_word_v1(int64_t handle, int64_t index, int64_t field) {
    if (handle != 1 || !resident || index < 0 || (uint64_t)index >= resident->function_count) return -1;
    const struct image_function *f = &functions(resident)[index];
    switch (field) { case 0: return f->id; case 1: return f->address; default: return -1; }
}
#else
int64_t simple_xray_image_snapshot_create_v1(int64_t a, int64_t b) { (void)a; (void)b; return SIMPLE_XRAY_IMAGE_UNSUPPORTED_V1; }
int64_t simple_xray_image_snapshot_word_v1(int64_t a, int64_t b) { (void)a; (void)b; return -1; }
int64_t simple_xray_image_snapshot_section_byte_v1(int64_t a, int64_t b) { (void)a; (void)b; return -1; }
int64_t simple_xray_image_snapshot_build_id_byte_v1(int64_t a, int64_t b) { (void)a; (void)b; return -1; }
int64_t simple_xray_image_snapshot_range_word_v1(int64_t a, int64_t b, int64_t c) { (void)a; (void)b; (void)c; return -1; }
int64_t simple_xray_image_snapshot_function_word_v1(int64_t a, int64_t b, int64_t c) { (void)a; (void)b; (void)c; return -1; }
#endif
