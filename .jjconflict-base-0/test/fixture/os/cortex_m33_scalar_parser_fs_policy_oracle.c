#include <stdint.h>
#include <stdio.h>

enum {
    TEXT_MISMATCH = 0,
    TEXT_ADVANCE = 1,
    TEXT_MATCHED = 2,
    FS_ADD_ADMITTED = 0,
    FS_ADD_TABLE_FULL = 1,
    FS_ADD_STORAGE_FULL = 2,
    FS_FIND_NEXT = 0,
    FS_FIND_FOUND = 1,
    FS_FIND_NOT_FOUND = 2
};

static uint32_t oracle_streq(uint32_t a, uint32_t b) {
    if (a != b) return TEXT_MISMATCH;
    if (a == 0) return TEXT_MATCHED;
    return TEXT_ADVANCE;
}

static uint32_t oracle_starts_with(uint32_t value, uint32_t prefix) {
    if (prefix == 0) return TEXT_MATCHED;
    if (value != prefix) return TEXT_MISMATCH;
    return TEXT_ADVANCE;
}

static uint32_t oracle_hex_prefix(uint32_t first, uint32_t second) {
    if (first != (uint32_t)'0') return 0;
    if ((second | UINT32_C(32)) == (uint32_t)'x') return 2;
    return 0;
}

static uint32_t oracle_hex_digit(uint32_t byte) {
    if (byte >= (uint32_t)'0' && byte <= (uint32_t)'9') return byte - (uint32_t)'0';
    if (byte >= (uint32_t)'a' && byte <= (uint32_t)'f') return byte - (uint32_t)'a' + 10;
    if (byte >= (uint32_t)'A' && byte <= (uint32_t)'F') return byte - (uint32_t)'A' + 10;
    return UINT32_MAX;
}

static uint32_t oracle_loop_step(uint32_t value) {
    return value == 0 ? 0u : 1u;
}

static uint32_t oracle_fs_add(uint32_t count, uint32_t used, uint32_t size,
                              uint32_t max_files, uint32_t storage_size) {
    uint32_t next_used;
    if (count >= max_files) return FS_ADD_TABLE_FULL;
    if (used > storage_size) return FS_ADD_STORAGE_FULL;
    if (size > storage_size - used) return FS_ADD_STORAGE_FULL;
    next_used = used + ((size + 3u) & UINT32_C(0xfffffffc));
    return next_used << 8;
}

static uint32_t oracle_fs_name(uint32_t byte, uint32_t index, uint32_t name_max) {
    if (byte == 0) return 0;
    if (index >= name_max - 1u) return 0;
    return 1;
}

static uint32_t oracle_fs_init(uint32_t index) {
    return index >= 6 ? UINT32_MAX : index;
}

static uint32_t oracle_fs_find(uint32_t index, uint32_t count, uint32_t equal) {
    if (index >= count) return FS_FIND_NOT_FOUND;
    if (equal != 0) return FS_FIND_FOUND;
    return FS_FIND_NEXT;
}

static void emit2(const char *group, const char *case_name,
                  uint32_t a, uint32_t b, uint32_t value) {
    printf("group=%s case=%s a=%u b=%u value=%u\n", group, case_name, a, b, value);
}

static void emit3(const char *group, const char *case_name,
                  uint32_t a, uint32_t b, uint32_t c, uint32_t value) {
    printf("group=%s case=%s a=%u b=%u c=%u value=%u\n",
           group, case_name, a, b, c, value);
}

static void emit5(const char *group, const char *case_name, uint32_t a,
                  uint32_t b, uint32_t c, uint32_t d, uint32_t e,
                  uint32_t value) {
    printf("group=%s case=%s a=%u b=%u c=%u d=%u e=%u value=%u\n",
           group, case_name, a, b, c, d, e, value);
}

int main(void) {
    static const uint32_t digit_matrix[] = {
        1, 47, 48, 57, 58, 64, 65, 70, 71, 96, 97, 102, 103
    };
    size_t i;

    emit2("streq", "advance", 65, 65, oracle_streq(65, 65));
    emit2("streq", "mismatch", 65, 66, oracle_streq(65, 66));
    emit2("streq", "matched", 0, 0, oracle_streq(0, 0));
    emit2("starts", "advance", 65, 65, oracle_starts_with(65, 65));
    emit2("starts", "mismatch", 65, 66, oracle_starts_with(65, 66));
    emit2("starts", "matched", 65, 0, oracle_starts_with(65, 0));
    emit2("prefix", "none-first", 49, 120, oracle_hex_prefix(49, 120));
    emit2("prefix", "none-second", 48, 113, oracle_hex_prefix(48, 113));
    emit2("prefix", "lower", 48, 120, oracle_hex_prefix(48, 120));
    emit2("prefix", "upper", 48, 88, oracle_hex_prefix(48, 88));
    for (i = 0; i < sizeof digit_matrix / sizeof digit_matrix[0]; i++)
        emit2("digit", "matrix", digit_matrix[i], 0,
              oracle_hex_digit(digit_matrix[i]));
    emit2("strlen", "stop", 0, 0, oracle_loop_step(0));
    emit2("strlen", "advance", 65, 0, oracle_loop_step(65));
    emit2("memcpy", "stop", 0, 0, oracle_loop_step(0));
    emit2("memcpy", "advance", 4, 0, oracle_loop_step(4));
    emit5("fs-add", "admit", 0, 0, 5, 16, 4096, oracle_fs_add(0, 0, 5, 16, 4096));
    emit5("fs-add", "table-full", 16, 0, 1, 16, 4096, oracle_fs_add(16, 0, 1, 16, 4096));
    emit5("fs-add", "used-invalid", 0, 4097, 0, 16, 4096, oracle_fs_add(0, 4097, 0, 16, 4096));
    emit5("fs-add", "storage-full", 0, 4095, 2, 16, 4096, oracle_fs_add(0, 4095, 2, 16, 4096));
    emit5("fs-add", "exact-fit", 15, 4092, 4, 16, 4096, oracle_fs_add(15, 4092, 4, 16, 4096));
    emit3("fs-name", "nul", 0, 0, 32, oracle_fs_name(0, 0, 32));
    emit3("fs-name", "advance", 65, 30, 32, oracle_fs_name(65, 30, 32));
    emit3("fs-name", "limit", 65, 31, 32, oracle_fs_name(65, 31, 32));
    emit2("fs-init", "first", 0, 0, oracle_fs_init(0));
    emit2("fs-init", "last", 5, 0, oracle_fs_init(5));
    emit2("fs-init", "done", 6, 0, oracle_fs_init(6));
    emit3("fs-find", "next", 0, 2, 0, oracle_fs_find(0, 2, 0));
    emit3("fs-find", "found", 1, 2, 1, oracle_fs_find(1, 2, 1));
    emit3("fs-find", "not-found", 2, 2, 0, oracle_fs_find(2, 2, 0));
    return 0;
}
