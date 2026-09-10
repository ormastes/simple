#include <stdint.h>

#ifndef KPF_PLUGIN_MAJOR
#define KPF_PLUGIN_MAJOR 1
#endif

#ifndef KPF_PLUGIN_MINOR
#define KPF_PLUGIN_MINOR 4
#endif

#ifndef KPF_PLUGIN_DIGEST
#define KPF_PLUGIN_DIGEST "sha256:image-v4"
#endif

#define KPF_INTERFACE_NAME "simple.sffi.Image"
#define KPF_CAPABILITY "image.decode"
#define KPF_CONTENT_DIGEST "sha256:native-matrix-fixture"

struct __attribute__((packed)) simple_plugin_entry_v1 {
    uint8_t magic[8];
    uint32_t total_size;
    uint32_t simple_abi_version;
    uint8_t simple_abi_deferred;
    uint8_t reserved[3];
    uint16_t major;
    uint16_t minor;
    uint16_t name_length;
    char name[sizeof(KPF_INTERFACE_NAME) - 1];
    uint16_t digest_length;
    char digest[sizeof(KPF_PLUGIN_DIGEST) - 1];
    uint16_t capability_count;
    uint16_t capability_length;
    char capability[sizeof(KPF_CAPABILITY) - 1];
    uint16_t plugin_digest_length;
    char plugin_digest[sizeof(KPF_CONTENT_DIGEST) - 1];
};

static const struct simple_plugin_entry_v1 descriptor = {
    .magic = {'S', 'P', 'L', 'P', 'E', 'V', '1', 0},
    .total_size = sizeof(struct simple_plugin_entry_v1),
    .simple_abi_version = 0,
    .simple_abi_deferred = 1,
    .reserved = {0, 0, 0},
    .major = KPF_PLUGIN_MAJOR,
    .minor = KPF_PLUGIN_MINOR,
    .name_length = sizeof(KPF_INTERFACE_NAME) - 1,
    .name = KPF_INTERFACE_NAME,
    .digest_length = sizeof(KPF_PLUGIN_DIGEST) - 1,
    .digest = KPF_PLUGIN_DIGEST,
    .capability_count = 1,
    .capability_length = sizeof(KPF_CAPABILITY) - 1,
    .capability = KPF_CAPABILITY,
    .plugin_digest_length = sizeof(KPF_CONTENT_DIGEST) - 1,
    .plugin_digest = KPF_CONTENT_DIGEST,
};

static uint64_t entry_calls;

__attribute__((visibility("default")))
intptr_t spl_plugin_entry_v1(void) {
    entry_calls += 1;
    return (intptr_t)&descriptor;
}

__attribute__((visibility("default"), noinline))
int64_t fixture_hot_call_v1(int64_t value) {
    return value * 3 + 1;
}

__attribute__((visibility("default")))
uint64_t fixture_entry_call_count_v1(void) {
    return entry_calls;
}
