#include "runtime_value.h"
#include <stdbool.h>

RuntimeValue rt_value_int(int64_t i) { return rv_from_int(i); }
RuntimeValue rt_value_float(double f) { return rv_from_float(f); }
RuntimeValue rt_value_bool(bool b) { return rv_from_bool(b); }
RuntimeValue rt_value_nil(void) { return RT_NIL; }

int64_t rt_value_as_int(RuntimeValue v) { return rv_to_int(v); }
double rt_value_as_float(RuntimeValue v) { return rv_to_float(v); }
bool rt_value_as_bool(RuntimeValue v) { return rv_to_bool(v); }

bool rt_value_truthy(RuntimeValue v) {
    uint64_t tag = rv_tag(v);
    if (tag == TAG_SPECIAL) {
        uint64_t p = rv_payload(v);
        if (p == SPECIAL_NIL || p == SPECIAL_FALSE) return false;
        return true;
    }
    if (tag == TAG_INT) return rv_to_int(v) != 0;
    if (tag == TAG_FLOAT) return rv_to_float(v) != 0.0;
    return true;
}

bool rt_value_is_nil(RuntimeValue v) { return rv_is_nil(v); }
bool rt_value_is_int(RuntimeValue v) { return rv_is_int(v); }
bool rt_value_is_float(RuntimeValue v) { return rv_is_float(v); }
bool rt_value_is_bool(RuntimeValue v) { return rv_is_bool(v); }
bool rt_value_is_heap(RuntimeValue v) { return rv_is_heap(v); }
uint8_t rt_value_type_tag(RuntimeValue v) { return (uint8_t)rv_tag(v); }
bool rt_is_error(RuntimeValue v) { return rv_is_error(v); }
