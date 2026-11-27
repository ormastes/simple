/* Cold, main-image profile association. The checked compiler issuer, not this
 * shape decoder, authenticates catalogue evidence against actual link inputs.
 * All mutable operations run under the process-wide resident control owner. */
#include "xray_qualification_profile_v1.h"
#include "xray_llvm_image_linux.h"
#include <stddef.h>
#include <string.h>
#if defined(__linux__) && defined(__x86_64__) && __SIZEOF_POINTER__ == 8 && \
    __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#include "xray_resident_descriptor_v1.h"
#include "xray_channel_producer_v1.h"
extern const unsigned char __start_simple_xray_profile_v1[] __attribute__((weak));
extern const unsigned char __stop_simple_xray_profile_v1[] __attribute__((weak));
extern const unsigned char __simple_xray_qualified_profile_v1[] __attribute__((weak));
extern int64_t simple_xray_resident_control_is_owned_v1(void);
extern int64_t simple_xray_startup_current_owner_v1(void);
extern int64_t simple_xray_resident_never_published_v1(void);
extern int64_t simple_xray_resident_descriptor_check_v1(int64_t);
extern int64_t simple_xray_llvm_resident_publish_v1(int64_t);
static unsigned char profile_copy[SIMPLE_XRAY_PROFILE_BYTES_V1];
static unsigned char profile_build_id[20];
static int64_t bound_snapshot;
static uint64_t profile_issued, publication_claimed;
static uint64_t read_word(const unsigned char *p) {
    uint64_t value = 0;
    for (unsigned i = 0; i < 8; ++i) value |= (uint64_t)p[i] << (i * 8);
    return value;
}
static int snapshot_matches(int64_t snapshot) {
    if (snapshot != bound_snapshot || simple_xray_image_snapshot_word_v1(snapshot, 0) != 1)
        return 0;
    for (int64_t i = 0; i < 20; ++i)
        if (simple_xray_image_snapshot_build_id_byte_v1(snapshot, i) != profile_build_id[i]) return 0;
    return 1;
}
static int shape_valid(const unsigned char *p) {
    uint64_t contexts = read_word(p + 48), payload = read_word(p + 56);
    uint64_t cap = read_word(p + 64);
    uint64_t profile = read_word(p + 32), evidence = read_word(p + 40);
    if (!((profile == 1 && evidence == 255) || (profile == 2 && evidence == 254))) return 0;
    if (read_word(p) != SIMPLE_XRAY_PROFILE_MAGIC_V1 || read_word(p + 8) != 1 ||
        read_word(p + 16) != 480 || read_word(p + 24) != 1 ||
        !contexts || contexts > 64 || !payload || payload > 393216 || payload % 96 ||
        cap > 67108864 || read_word(p + 72) != 1 ||
        read_word(p + 80) != 33554432 || read_word(p + 88) != 8) return 0;
    uint64_t needed = UINT64_C(33554432) + 80 + 64 + contexts * (32 + 128 + payload) + 4096 * 16 + 96;
    if (cap < needed) return 0;
    for (unsigned i = 96; i < 128; ++i) if (p[i]) return 0;
    for (unsigned digest = 0; digest < 11; ++digest) {
        unsigned any = 0;
        for (unsigned byte = 0; byte < 32; ++byte) any |= p[128 + digest * 32 + byte];
        if (profile == 2 && digest == 7) {
            if (any) return 0;
        } else if (!any) return 0;
    }
    return 1;
}
int64_t simple_xray_resident_profile_bind_v1(int64_t snapshot) {
    if (!simple_xray_resident_control_is_owned_v1()) return SIMPLE_XRAY_PROFILE_OWNER_V1;
    if (__atomic_load_n(&profile_issued, __ATOMIC_ACQUIRE))
        return snapshot_matches(snapshot) ? 1 : SIMPLE_XRAY_PROFILE_SNAPSHOT_V1;
    if (simple_xray_image_snapshot_word_v1(snapshot, 0) != 1 ||
        simple_xray_image_snapshot_word_v1(snapshot, 5) != 20 ||
        simple_xray_image_snapshot_word_v1(snapshot, 4) <= 0 ||
        simple_xray_image_snapshot_word_v1(snapshot, 4) > 4096 ||
        simple_xray_image_snapshot_word_v1(snapshot, 6) <= 0 ||
        simple_xray_image_snapshot_word_v1(snapshot, 6) > SIMPLE_XRAY_PROFILE_METADATA_RESERVE_V1)
        return SIMPLE_XRAY_PROFILE_SNAPSHOT_V1;
    uintptr_t start = (uintptr_t)__start_simple_xray_profile_v1;
    uintptr_t stop = (uintptr_t)__stop_simple_xray_profile_v1;
    uintptr_t symbol = (uintptr_t)__simple_xray_qualified_profile_v1;
    if (!start && !stop && !symbol) return SIMPLE_XRAY_PROFILE_ABSENT_V1;
    if (!start || !stop || symbol != start || start % 8 || start > INT64_MAX ||
        stop <= start || stop - start != 480 || stop > INT64_MAX)
        return SIMPLE_XRAY_PROFILE_INVALID_V1;
    int64_t ranges = simple_xray_image_snapshot_word_v1(snapshot, 3);
    if (ranges <= 0 || ranges > SIMPLE_XRAY_IMAGE_MAX_RANGES_V1)
        return SIMPLE_XRAY_PROFILE_SNAPSHOT_V1;
    int contained = 0;
    for (int64_t i = 0; i < ranges; ++i) {
        int64_t address = simple_xray_image_snapshot_range_word_v1(snapshot, i, 0);
        int64_t size = simple_xray_image_snapshot_range_word_v1(snapshot, i, 1);
        int64_t flags = simple_xray_image_snapshot_range_word_v1(snapshot, i, 2);
        if (address < 0 || size <= 0 || address > INT64_MAX - size || flags < 0)
            return SIMPLE_XRAY_PROFILE_SNAPSHOT_V1;
        if ((flags & 1) && !(flags & 2) && start >= (uint64_t)address &&
            stop <= (uint64_t)address + (uint64_t)size) contained = 1;
    }
    if (!contained) return SIMPLE_XRAY_PROFILE_INVALID_V1;
    const unsigned char *record = (const unsigned char *)start;
    if (!shape_valid(record)) return SIMPLE_XRAY_PROFILE_INVALID_V1;
    for (int64_t i = 0; i < 20; ++i) {
        int64_t byte = simple_xray_image_snapshot_build_id_byte_v1(snapshot, i);
        if (byte < 0 || byte > 255) return SIMPLE_XRAY_PROFILE_SNAPSHOT_V1;
        profile_build_id[i] = (unsigned char)byte;
    }
    memcpy(profile_copy, record, sizeof(profile_copy));
    bound_snapshot = snapshot;
    __atomic_store_n(&profile_issued, 1, __ATOMIC_RELEASE);
    return 1;
}
int64_t simple_xray_resident_profile_word_v1(int64_t handle, int64_t field) {
    if (handle != 1 || !__atomic_load_n(&profile_issued, __ATOMIC_ACQUIRE) || field < 0 || field >= 12)
        return SIMPLE_XRAY_PROFILE_INVALID_V1;
    return (int64_t)read_word(profile_copy + field * 8);
}
int64_t simple_xray_resident_profile_digest_word_v1(int64_t handle, int64_t digest, int64_t word) {
    if (handle != 1 || !__atomic_load_n(&profile_issued, __ATOMIC_ACQUIRE) ||
        digest < 0 || digest >= 11 || word < 0 || word >= 8) return SIMPLE_XRAY_PROFILE_INVALID_V1;
    const unsigned char *p = profile_copy + 128 + digest * 32 + word * 4;
    return (int64_t)((uint32_t)p[0] | (uint32_t)p[1] << 8 |
                     (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24);
}
int64_t simple_xray_llvm_resident_publish_qualified_v1(int64_t handle,
        int64_t snapshot, int64_t descriptor, int64_t generation) {
    if (handle != 1 || !__atomic_load_n(&profile_issued, __ATOMIC_ACQUIRE) ||
        !simple_xray_startup_current_owner_v1() || !snapshot_matches(snapshot) ||
        !simple_xray_resident_never_published_v1() ||
        !simple_xray_resident_descriptor_check_v1(descriptor)) return 0;
    const SimpleXrayResidentDescriptorV1 *d = (const void *)(intptr_t)descriptor;
    const SimpleXrayThreadContextHeaderV1 *pool = (const void *)(uintptr_t)d->pool;
    uint64_t contexts = pool->max_slots;
    if (generation <= 0 || d->generation != (uint64_t)generation || d->module_instance != 1 ||
        !contexts || contexts > read_word(profile_copy + 48)) return 0;
    const SimpleXrayThreadContextSlotV1 *slots = (const void *)((const unsigned char *)pool + 64);
    uint64_t total = UINT64_C(33554432) + 80 + d->pool_bytes + d->map_count * 16 + 96;
    for (uint64_t i = 0; i < contexts; ++i) {
        const uint64_t *arena = (const void *)(uintptr_t)slots[i].arena;
        uint64_t payload = arena[CH_CAPACITY] * 96;
        if (payload > read_word(profile_copy + 56) || slots[i].bytes > UINT64_C(393344)) return 0;
        total += slots[i].bytes;
    }
    if (total > read_word(profile_copy + 64)) return 0;
    const SimpleXrayResidentBindingV1 *map = (const void *)(uintptr_t)d->map;
    for (uint64_t i = 0; i < d->map_count; ++i)
        if (simple_xray_image_snapshot_function_word_v1(snapshot, (int64_t)map[i].llvm_id - 1, 0) !=
                (int64_t)map[i].llvm_id) return 0;
    uint64_t expected = 0;
    if (!__atomic_compare_exchange_n(&publication_claimed, &expected, 1, 0,
                                    __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return 0;
    /* Count an attempted publication, not a numeric generation. Never refund
     * this claim after failure: a later attempt cannot reconfigure this image. */
    return simple_xray_llvm_resident_publish_v1(descriptor);
}
#else
int64_t simple_xray_resident_profile_bind_v1(int64_t snapshot) { (void)snapshot; return SIMPLE_XRAY_PROFILE_UNSUPPORTED_V1; }
int64_t simple_xray_resident_profile_word_v1(int64_t h, int64_t f) { (void)h; (void)f; return SIMPLE_XRAY_PROFILE_INVALID_V1; }
int64_t simple_xray_resident_profile_digest_word_v1(int64_t h, int64_t d, int64_t w) { (void)h; (void)d; (void)w; return SIMPLE_XRAY_PROFILE_INVALID_V1; }
int64_t simple_xray_llvm_resident_publish_qualified_v1(int64_t h, int64_t s, int64_t d, int64_t g) { (void)h; (void)s; (void)d; (void)g; return 0; }
#endif
