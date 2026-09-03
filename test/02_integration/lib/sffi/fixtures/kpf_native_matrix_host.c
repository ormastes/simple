#include <dlfcn.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define ENTRY_SYMBOL "spl_plugin_entry_v1"
#define HOT_SYMBOL "fixture_hot_call_v1"
#define COUNT_SYMBOL "fixture_entry_call_count_v1"
#define HOST_INTERFACE "simple.sffi.Image"
#define HOST_DIGEST "sha256:image-v4"
#define OLDER_DIGEST "sha256:image-v2"
#define HOT_ITERATIONS UINT64_C(4000000)
#define SAMPLE_COUNT 7

typedef intptr_t (*entry_fn)(void);
typedef int64_t (*hot_fn)(int64_t);
typedef uint64_t (*count_fn)(void);

struct admitted_plugin {
    void *library;
    hot_fn hot;
    count_fn entry_count;
};

struct byte_reader {
    const uint8_t *bytes;
    uint32_t size;
    uint32_t offset;
};

static uint16_t read_u16(struct byte_reader *reader) {
    uint16_t value;
    if (reader->offset + 2 > reader->size) exit(90);
    value = (uint16_t)reader->bytes[reader->offset]
        | (uint16_t)((uint16_t)reader->bytes[reader->offset + 1] << 8);
    reader->offset += 2;
    return value;
}

static int read_text_equals(struct byte_reader *reader, const char *expected) {
    uint16_t size = read_u16(reader);
    size_t expected_size = strlen(expected);
    int equal;
    if (reader->offset + size > reader->size) exit(91);
    equal = size == expected_size
        && memcmp(reader->bytes + reader->offset, expected, size) == 0;
    reader->offset += size;
    return equal;
}

static int negotiate_descriptor(const uint8_t *bytes, const char **reason) {
    struct byte_reader reader;
    uint32_t total_size;
    uint32_t simple_abi;
    uint8_t deferred;
    uint16_t major;
    uint16_t minor;
    uint16_t capability_count;
    int name_matches;
    int digest_matches;
    int capability_matches;

    if (memcmp(bytes, "SPLPEV1\0", 8) != 0) {
        *reason = "entry";
        return 0;
    }
    memcpy(&total_size, bytes + 8, sizeof(total_size));
    if (total_size < 24 || total_size > 4096) {
        *reason = "entry";
        return 0;
    }
    memcpy(&simple_abi, bytes + 12, sizeof(simple_abi));
    deferred = bytes[16];
    if (simple_abi != 0 || deferred != 1 || bytes[17] || bytes[18] || bytes[19]) {
        *reason = "abi";
        return 0;
    }
    reader.bytes = bytes;
    reader.size = total_size;
    reader.offset = 20;
    major = read_u16(&reader);
    minor = read_u16(&reader);
    name_matches = read_text_equals(&reader, HOST_INTERFACE);
    digest_matches = read_text_equals(&reader, HOST_DIGEST);
    if (!digest_matches) {
        uint32_t digest_offset = reader.offset;
        reader.offset = 24;
        (void)read_text_equals(&reader, HOST_INTERFACE);
        digest_matches = read_text_equals(&reader, OLDER_DIGEST);
        reader.offset = digest_offset;
    }
    capability_count = read_u16(&reader);
    capability_matches = capability_count == 1
        && read_text_equals(&reader, "image.decode");
    (void)read_text_equals(&reader, "sha256:native-matrix-fixture");
    if (reader.offset != reader.size || !name_matches || !capability_matches) {
        *reason = "entry";
        return 0;
    }
    if (major != 1) {
        *reason = "major";
        return 0;
    }
    if (minor > 4) {
        *reason = "minor";
        return 0;
    }
#ifndef KPF_TEST_SKIP_DIGEST_CHECK
    if (!digest_matches) {
        *reason = "digest";
        return 0;
    }
#endif
    *reason = "accepted";
    return 1;
}

static int admit(const char *path, struct admitted_plugin *result, const char **reason) {
    entry_fn entry;
    const uint8_t *descriptor;
    void *library = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (library == NULL) {
        *reason = "open";
        return 0;
    }
    entry = (entry_fn)dlsym(library, ENTRY_SYMBOL);
    if (entry == NULL) {
        dlclose(library);
        *reason = "symbol";
        return 0;
    }
    descriptor = (const uint8_t *)(uintptr_t)entry();
    if (descriptor == NULL || !negotiate_descriptor(descriptor, reason)) {
        dlclose(library);
        return 0;
    }
    result->hot = (hot_fn)dlsym(library, HOT_SYMBOL);
    result->entry_count = (count_fn)dlsym(library, COUNT_SYMBOL);
    if (result->hot == NULL || result->entry_count == NULL) {
        dlclose(library);
        *reason = "operation";
        return 0;
    }
    result->library = library;
    return 1;
}

static uint64_t monotonic_ns(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0) exit(92);
    return (uint64_t)value.tv_sec * UINT64_C(1000000000) + (uint64_t)value.tv_nsec;
}

static uint64_t timed_window(hot_fn hot, uint64_t seed) {
    volatile int64_t total = 0;
    uint64_t begin = monotonic_ns();
    uint64_t index;
    for (index = 0; index < HOT_ITERATIONS; ++index) {
        total += hot((int64_t)(index ^ seed));
    }
    if (total == INT64_MIN) exit(93);
    return monotonic_ns() - begin;
}

static int compare_u64(const void *left, const void *right) {
    uint64_t a = *(const uint64_t *)left;
    uint64_t b = *(const uint64_t *)right;
    return (a > b) - (a < b);
}

static int verify_resident_cost(const char *path) {
    struct admitted_plugin plugin;
    const char *reason;
    uint64_t first[SAMPLE_COUNT];
    uint64_t second[SAMPLE_COUNT];
    uint64_t first_median;
    uint64_t second_median;
    uint64_t larger;
    uint64_t smaller;
    int sample;

    if (!admit(path, &plugin, &reason)) return 20;
    if (plugin.entry_count() != 1) return 21;
    (void)timed_window(plugin.hot, 0);
    for (sample = 0; sample < SAMPLE_COUNT; ++sample) {
        first[sample] = timed_window(plugin.hot, (uint64_t)sample + 1);
        second[sample] = timed_window(plugin.hot, (uint64_t)sample + 17);
    }
    if (plugin.entry_count() != 1) return 22;
    qsort(first, SAMPLE_COUNT, sizeof(first[0]), compare_u64);
    qsort(second, SAMPLE_COUNT, sizeof(second[0]), compare_u64);
    first_median = first[SAMPLE_COUNT / 2];
    second_median = second[SAMPLE_COUNT / 2];
    larger = first_median > second_median ? first_median : second_median;
    smaller = first_median < second_median ? first_median : second_median;
    printf("resident_hot_call first_ns_per_call=%.3f second_ns_per_call=%.3f ratio=%.4f entry_calls=%" PRIu64 "\n",
        (double)first_median / (double)HOT_ITERATIONS,
        (double)second_median / (double)HOT_ITERATIONS,
        (double)larger / (double)smaller,
        plugin.entry_count());
    dlclose(plugin.library);
    return larger * 100 > smaller * 125 ? 23 : 0;
}

static int expect_case(const char *label, const char *path, int accepted,
        const char *expected_reason) {
    struct admitted_plugin plugin;
    const char *reason = "none";
    int actual = admit(path, &plugin, &reason);
    if (actual) dlclose(plugin.library);
    printf("matrix_case name=%s result=%s reason=%s\n", label,
        actual ? "accepted" : "rejected", reason);
    if (actual != accepted || strcmp(reason, expected_reason) != 0) return 1;
    return 0;
}

int main(int argc, char **argv) {
    int failures = 0;
    if (argc != 5) return 64;
    failures += expect_case("matching-major", argv[1], 1, "accepted");
    failures += expect_case("older-compatible-minor", argv[2], 1, "accepted");
    failures += expect_case("wrong-major", argv[3], 0, "major");
    failures += expect_case("digest-mismatch", argv[4], 0, "digest");
    if (failures != 0) return 65;
    failures = verify_resident_cost(argv[1]);
    if (failures != 0) return failures;
    puts("KPF_NATIVE_DYNAMIC_MATRIX: PASS");
    return 0;
}
