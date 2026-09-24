#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#ifndef PLUGIN_MAJOR
#define PLUGIN_MAJOR 1
#endif
#ifndef PLUGIN_MINOR
#define PLUGIN_MINOR 2
#endif
#ifndef PLUGIN_DIGEST
#define PLUGIN_DIGEST "sha256:image-v2"
#endif
#ifndef PLUGIN_IFACE_NAME
#define PLUGIN_IFACE_NAME "simple.sffi.Image"
#endif
#ifndef PLUGIN_ABI
#define PLUGIN_ABI 0
#endif
#ifndef PLUGIN_DEFERRED
#define PLUGIN_DEFERRED 1
#endif
#ifndef PLUGIN_CAPABILITY
#define PLUGIN_CAPABILITY "image.decode"
#endif
#ifndef PLUGIN_MAGIC_0
#define PLUGIN_MAGIC_0 'S'
#endif
static const char iface_name[] = PLUGIN_IFACE_NAME;
static const char abi_digest[] = PLUGIN_DIGEST;
static const char required_capability[] = PLUGIN_CAPABILITY;
static const char content_digest[] = "sha256:fixture-content";
struct __attribute__((packed)) plugin_entry_v1 {
    uint8_t magic[8]; uint32_t total_size; uint32_t simple_abi_version;
    uint8_t simple_abi_deferred; uint8_t reserved[3];
    uint16_t major; uint16_t minor;
    uint16_t name_len; char name[sizeof(iface_name) - 1];
    uint16_t digest_len; char digest[sizeof(abi_digest) - 1];
    uint16_t capability_count;
    uint16_t capability_len; char capability[sizeof(required_capability) - 1];
    uint16_t plugin_digest_len; char plugin_digest[sizeof(content_digest) - 1];
};
static const struct plugin_entry_v1 descriptor = {
    .magic = {PLUGIN_MAGIC_0, 'P', 'L', 'P', 'E', 'V', '1', 0},
    .total_size = sizeof(struct plugin_entry_v1), .simple_abi_version = PLUGIN_ABI,
    .simple_abi_deferred = PLUGIN_DEFERRED, .reserved = {0, 0, 0},
    .major = PLUGIN_MAJOR, .minor = PLUGIN_MINOR,
    .name_len = sizeof(iface_name) - 1, .name = PLUGIN_IFACE_NAME,
    .digest_len = sizeof(abi_digest) - 1, .digest = PLUGIN_DIGEST,
    .capability_count = 1,
    .capability_len = sizeof(required_capability) - 1,
    .capability = PLUGIN_CAPABILITY,
    .plugin_digest_len = sizeof(content_digest) - 1,
    .plugin_digest = "sha256:fixture-content",
};
#ifndef OMIT_PLUGIN_ENTRY
intptr_t spl_plugin_entry_v1(void) {
#ifdef PLUGIN_NULL_ENTRY
    return 0;
#else
    return (intptr_t)&descriptor;
#endif
}
#endif
intptr_t fixture_product_symbol(void) { return 73; }

__attribute__((destructor)) static void fixture_unloaded(void) {
    const char *marker = getenv("SIMPLE_PHASE6_UNLOAD_MARKER");
    if (marker != NULL && marker[0] != '\0') {
        FILE *file = fopen(marker, "w");
        if (file != NULL) {
            fputs("closed\n", file);
            fclose(file);
        }
    }
}
