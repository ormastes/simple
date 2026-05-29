#include "runtime_value.h"
#include <stdint.h>
#include <stdio.h>

RuntimeValue rt_function_not_found(const uint8_t *name_ptr, uint64_t name_len) {
    if (!name_ptr) {
        fprintf(stderr, "Runtime error: Function not found (unknown name)\n");
    } else {
        fprintf(stderr, "Runtime error: Function '%.*s' not found\n",
                (int)name_len, (const char *)name_ptr);
    }
    return RT_ERROR;
}

RuntimeValue rt_method_not_found(const uint8_t *type_ptr, uint64_t type_len,
                                  const uint8_t *method_ptr, uint64_t method_len) {
    const char *tname = type_ptr ? (const char *)type_ptr : "<unknown type>";
    int tlen = type_ptr ? (int)type_len : 14;
    const char *mname = method_ptr ? (const char *)method_ptr : "<unknown method>";
    int mlen = method_ptr ? (int)method_len : 16;

    fprintf(stderr, "Runtime error: Method '%.*s' not found on type '%.*s'\n",
            mlen, mname, tlen, tname);
    return RT_ERROR;
}
