#include "runtime_string_ffi.h"
#include "runtime.h"

#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* Copy a foreign NUL-terminated string into a runtime-owned text value.
 * Ownership of the source pointer remains with the foreign API. */
int64_t rt_cstring_to_text(int64_t cstr_value) {
    const char *cstr = (const char *)(uintptr_t)cstr_value;
    if (!cstr) return rt_string_new(NULL, 0);
    return rt_string_new((const uint8_t *)cstr, (uint64_t)strlen(cstr));
}
