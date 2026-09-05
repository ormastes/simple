#ifndef SIMPLEOS_ARM_FS_PATH_CLASSIFIER_H
#define SIMPLEOS_ARM_FS_PATH_CLASSIFIER_H

#include <stddef.h>
#include <stdint.h>

enum arm_fs_path_route_v1 {
    ARM_FS_ROUTE_REJECT = 0,
    ARM_FS_ROUTE_ROOT_QEMU_NONCE = 1,
    ARM_FS_ROUTE_ROOT_FS_EXEC = 2,
    ARM_FS_ROUTE_ROOT_SIMPLE = 3,
    ARM_FS_ROUTE_ROOT_HELLO_SPL = 4,
    ARM_FS_ROUTE_SYS_APPS = 10,
    ARM_FS_ROUTE_SYS = 11
};

static int arm_fs_bytes_equal(const char *bytes, size_t len, const char *literal, size_t literal_len)
{
    if (!bytes || len != literal_len) return 0;
    for (size_t i = 0; i < len; i++) if ((uint8_t)bytes[i] != (uint8_t)literal[i]) return 0;
    return 1;
}

static int arm_fs_bytes_prefix(const char *bytes, size_t len, const char *literal, size_t literal_len)
{
    if (!bytes || len <= literal_len) return 0;
    for (size_t i = 0; i < literal_len; i++) if ((uint8_t)bytes[i] != (uint8_t)literal[i]) return 0;
    return 1;
}

static uint32_t arm_fs_classify_path_bytes(const char *bytes, size_t len)
{
#define ARM_FS_EXACT(text, code) if (arm_fs_bytes_equal(bytes, len, text, sizeof(text) - 1)) return code
    ARM_FS_EXACT("/QEMUNONC.TXT", ARM_FS_ROUTE_ROOT_QEMU_NONCE);
    ARM_FS_EXACT("/FSEXEC.ELF", ARM_FS_ROUTE_ROOT_FS_EXEC);
    ARM_FS_EXACT("/SIMPLE.ELF", ARM_FS_ROUTE_ROOT_SIMPLE);
    ARM_FS_EXACT("/HELLO.SPL", ARM_FS_ROUTE_ROOT_HELLO_SPL);
#undef ARM_FS_EXACT
    if (arm_fs_bytes_equal(bytes, len, "/SYS/APPS/", sizeof("/SYS/APPS/") - 1)) return ARM_FS_ROUTE_REJECT;
    if (arm_fs_bytes_equal(bytes, len, "/SYS/", sizeof("/SYS/") - 1)) return ARM_FS_ROUTE_REJECT;
    if (arm_fs_bytes_prefix(bytes, len, "/SYS/APPS/", sizeof("/SYS/APPS/") - 1)) return ARM_FS_ROUTE_SYS_APPS;
    if (arm_fs_bytes_prefix(bytes, len, "/SYS/", sizeof("/SYS/") - 1)) return ARM_FS_ROUTE_SYS;
    return ARM_FS_ROUTE_REJECT;
}

struct arm_fs_runtime_string_v1 {
    uint32_t type;
    uint32_t size;
    uint64_t len;
    char data[];
};

enum arm_fs_runtime_string_reason_v1 {
    ARM_FS_TEXT_ACCEPTED = 0,
    ARM_FS_TEXT_OUTSIDE_HEAP = 1,
    ARM_FS_TEXT_SHORT_HEADER = 2,
    ARM_FS_TEXT_WRONG_TYPE = 3,
    ARM_FS_TEXT_LENGTH_LIMIT = 4,
    ARM_FS_TEXT_TRUNCATED = 5,
    ARM_FS_TEXT_SMALL_OBJECT = 6,
    ARM_FS_TEXT_MISSING_NUL = 7,
    ARM_FS_TEXT_UNKNOWN_PATH = 8
};

struct arm_fs_runtime_string_receipt_v1 {
    uint64_t raw;
    uintptr_t candidate;
    uintptr_t heap_base;
    uintptr_t heap_used_end;
    uint64_t len;
    uint32_t tag;
    uint32_t type;
    uint32_t size;
    uint32_t reason;
    uint32_t route;
};

static uint32_t arm_fs_classify_runtime_string_receipt(
    uint64_t value, uintptr_t heap_base, uintptr_t heap_used_end,
    uint32_t heap_string_type, struct arm_fs_runtime_string_receipt_v1 *receipt)
{
    struct arm_fs_runtime_string_receipt_v1 local = {0};
    local.raw = value;
    local.tag = (uint32_t)(value & 7ULL);
    local.candidate = local.tag == 1U ? (uintptr_t)(value & ~7ULL) : (uintptr_t)value;
    local.heap_base = heap_base;
    local.heap_used_end = heap_used_end;
#define ARM_FS_RECEIPT_RETURN(why) do { local.reason = (why); if (receipt) *receipt = local; return local.route; } while (0)
    if (local.candidate < heap_base || local.candidate > heap_used_end)
        ARM_FS_RECEIPT_RETURN(ARM_FS_TEXT_OUTSIDE_HEAP);
    if (heap_used_end - local.candidate < sizeof(struct arm_fs_runtime_string_v1))
        ARM_FS_RECEIPT_RETURN(ARM_FS_TEXT_SHORT_HEADER);
    const struct arm_fs_runtime_string_v1 *text =
        (const struct arm_fs_runtime_string_v1 *)local.candidate;
    local.type = text->type;
    local.size = text->size;
    local.len = text->len;
    if (text->type != heap_string_type) ARM_FS_RECEIPT_RETURN(ARM_FS_TEXT_WRONG_TYPE);
    if (text->len > 4096ULL) ARM_FS_RECEIPT_RETURN(ARM_FS_TEXT_LENGTH_LIMIT);
    size_t required = sizeof(*text) + (size_t)text->len + 1U;
    if (required < sizeof(*text) || required > heap_used_end - local.candidate)
        ARM_FS_RECEIPT_RETURN(ARM_FS_TEXT_TRUNCATED);
    if (text->size < required) ARM_FS_RECEIPT_RETURN(ARM_FS_TEXT_SMALL_OBJECT);
    if (text->data[text->len] != '\0') ARM_FS_RECEIPT_RETURN(ARM_FS_TEXT_MISSING_NUL);
    local.route = arm_fs_classify_path_bytes(text->data, (size_t)text->len);
    ARM_FS_RECEIPT_RETURN(local.route == ARM_FS_ROUTE_REJECT ? ARM_FS_TEXT_UNKNOWN_PATH : ARM_FS_TEXT_ACCEPTED);
#undef ARM_FS_RECEIPT_RETURN
}

static uint32_t arm_fs_classify_runtime_string(uint64_t value,
                                               uintptr_t heap_base,
                                               uintptr_t heap_used_end,
                                               uint32_t heap_string_type)
{
    return arm_fs_classify_runtime_string_receipt(value, heap_base,
        heap_used_end, heap_string_type, (struct arm_fs_runtime_string_receipt_v1 *)0);
}

#endif
