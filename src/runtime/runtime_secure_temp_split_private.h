/* Shared boxed-text adapters for mutually exclusive full-C and Rust-bootstrap
 * runtime owners. Directory creation stays with the real OS provider. */
#ifndef SIMPLE_RUNTIME_SECURE_TEMP_SPLIT_PRIVATE_H
#define SIMPLE_RUNTIME_SECURE_TEMP_SPLIT_PRIVATE_H
#include "runtime.h"
#include <string.h>

static _Thread_local char spl_secure_temp_parent_slot[4096];
static _Thread_local char spl_secure_temp_prefix_slot[128];
static _Thread_local int spl_secure_temp_parent_ready;
static _Thread_local int spl_secure_temp_prefix_ready;

static int spl_secure_temp_slot_from_value(int64_t value, char* slot,
                                           size_t capacity) {
    int64_t length = rt_string_len(value);
    if (length <= 0 || (uint64_t)length >= capacity) return 0;
    const uint8_t* bytes = rt_string_data(value);
    if (!bytes || memchr(bytes, 0, (size_t)length)) return 0;
    memcpy(slot, bytes, (size_t)length);
    slot[length] = 0;
    return 1;
}

int64_t rt_secure_temp_dir_set_parent(int64_t parent_value) {
    /* A refused replacement must not leave an earlier parent usable. */
    spl_secure_temp_parent_ready = 0;
    if (!spl_secure_temp_slot_from_value(parent_value,
            spl_secure_temp_parent_slot, sizeof(spl_secure_temp_parent_slot)))
        return 0;
    spl_secure_temp_parent_ready = 1;
    return 1;
}

int64_t rt_secure_temp_dir_set_prefix(int64_t prefix_value) {
    /* Decode may overwrite bytes before prefix validation refuses them. */
    spl_secure_temp_prefix_ready = 0;
    if (!spl_secure_temp_slot_from_value(prefix_value,
            spl_secure_temp_prefix_slot, sizeof(spl_secure_temp_prefix_slot)))
        return 0;
    if (strchr(spl_secure_temp_prefix_slot, '/') ||
            strchr(spl_secure_temp_prefix_slot, '\\')) return 0;
    spl_secure_temp_prefix_ready = 1;
    return 1;
}

int64_t rt_secure_temp_dir_make(void) {
    if (!spl_secure_temp_parent_ready || !spl_secure_temp_prefix_ready) {
        spl_secure_temp_parent_ready = 0;
        spl_secure_temp_prefix_ready = 0;
        return rt_string_new(NULL, 0);
    }
    char parent[sizeof(spl_secure_temp_parent_slot)];
    char prefix[sizeof(spl_secure_temp_prefix_slot)];
    memcpy(parent, spl_secure_temp_parent_slot, sizeof(parent));
    memcpy(prefix, spl_secure_temp_prefix_slot, sizeof(prefix));
    /* Consume both slots before entering the OS provider, including refusal. */
    spl_secure_temp_parent_ready = 0;
    spl_secure_temp_prefix_ready = 0;
    return rt_secure_temp_dir((const uint8_t*)parent, (uint64_t)strlen(parent),
                             (const uint8_t*)prefix, (uint64_t)strlen(prefix));
}
#endif
