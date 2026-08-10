#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "runtime.h"

static const char* simple_contract_kind_name(int64_t kind) {
    switch (kind) {
        case 1: return "Postcondition";
        case 2: return "Error postcondition";
        case 3: return "Entry invariant";
        case 4: return "Exit invariant";
        case 5: return "Assertion";
        default: return "Precondition";
    }
}

static void simple_contract_abort(void) {
    (void)rt_terminal_disable_raw_mode();
    rt_terminal_signal_scope_emergency_restore();
    abort();
}

void simple_contract_check(int64_t condition, int64_t kind,
                           const uint8_t* func_name, int64_t func_name_len) {
    if (condition != 0) return;
    fprintf(stderr, "%s violation in function '%.*s': contract condition failed\n",
            simple_contract_kind_name(kind),
            func_name && func_name_len > 0 ? (int)func_name_len : 9,
            func_name && func_name_len > 0 ? (const char*)func_name : "<unknown>");
    simple_contract_abort();
}

void simple_contract_check_msg(int64_t condition, int64_t kind,
                               const uint8_t* func_name, int64_t func_name_len,
                               const uint8_t* message, int64_t message_len) {
    if (condition != 0) return;
    fprintf(stderr, "%s violation in function '%.*s': contract condition failed",
            simple_contract_kind_name(kind),
            func_name && func_name_len > 0 ? (int)func_name_len : 9,
            func_name && func_name_len > 0 ? (const char*)func_name : "<unknown>");
    if (message && message_len > 0) {
        fprintf(stderr, " (%.*s)", (int)message_len, (const char*)message);
    }
    fputc('\n', stderr);
    simple_contract_abort();
}
