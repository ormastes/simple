#ifndef SIMPLE_RUNTIME_STRING_FFI_H
#define SIMPLE_RUNTIME_STRING_FFI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

int64_t rt_cstring_to_text(const char *cstr);

#ifdef __cplusplus
}
#endif

#endif
