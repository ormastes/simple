#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *contract_kind_name(int64_t kind) {
    switch (kind) {
        case 0: return "Precondition";
        case 1: return "Postcondition";
        case 2: return "Error postcondition";
        case 3: return "Entry invariant";
        case 4: return "Exit invariant";
        case 5: return "Assertion";
        default: return "Precondition";
    }
}

void simple_contract_check(
    int64_t condition,
    int64_t kind,
    const uint8_t *func_name_ptr,
    int64_t func_name_len
) {
    if (condition != 0) return;

    const char *kind_name = contract_kind_name(kind);
    if (func_name_ptr && func_name_len > 0) {
        fprintf(stderr, "%s violation in function '%.*s': contract condition failed\n",
                kind_name, (int)func_name_len, (const char *)func_name_ptr);
    } else {
        fprintf(stderr, "%s violation in function '<unknown>': contract condition failed\n",
                kind_name);
    }
    abort();
}

void simple_contract_check_msg(
    int64_t condition,
    int64_t kind,
    const uint8_t *func_name_ptr,
    int64_t func_name_len,
    const uint8_t *message_ptr,
    int64_t message_len
) {
    if (condition != 0) return;

    const char *kind_name = contract_kind_name(kind);
    const char *fname = "<unknown>";
    int fname_len = 9;
    if (func_name_ptr && func_name_len > 0) {
        fname = (const char *)func_name_ptr;
        fname_len = (int)func_name_len;
    }

    if (message_ptr && message_len > 0) {
        fprintf(stderr, "%s violation in function '%.*s': contract condition failed (%.*s)\n",
                kind_name, fname_len, fname, (int)message_len, (const char *)message_ptr);
    } else {
        fprintf(stderr, "%s violation in function '%.*s': contract condition failed\n",
                kind_name, fname_len, fname);
    }
    abort();
}
