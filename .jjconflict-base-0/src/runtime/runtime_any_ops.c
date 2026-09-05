#include "runtime_any_ops.h"
#include "runtime.h"

#include <limits.h>
#include <math.h>

static double any_as_f64(int64_t value) {
    return rt_value_is_float(value) ? rt_value_as_float(value) : (double)rt_value_as_int(value);
}

int64_t rt_any_sub(int64_t left, int64_t right) {
    if (rt_value_is_float(left) || rt_value_is_float(right))
        return rt_value_float(any_as_f64(left) - any_as_f64(right));
    return rt_value_int(rt_value_as_int(left) - rt_value_as_int(right));
}

int64_t rt_any_mul(int64_t left, int64_t right) {
    if (rt_value_is_float(left) || rt_value_is_float(right))
        return rt_value_float(any_as_f64(left) * any_as_f64(right));
    return rt_value_int(rt_value_as_int(left) * rt_value_as_int(right));
}

int64_t rt_any_div(int64_t left, int64_t right) {
    if (rt_value_is_float(left) || rt_value_is_float(right))
        return rt_value_float(any_as_f64(left) / any_as_f64(right));
    int64_t l = rt_value_as_int(left), r = rt_value_as_int(right);
    return rt_value_int(r == 0 || (l == INT64_MIN && r == -1) ? 0 : l / r);
}

int64_t rt_any_mod(int64_t left, int64_t right) {
    if (rt_value_is_float(left) || rt_value_is_float(right))
        return rt_value_float(fmod(any_as_f64(left), any_as_f64(right)));
    int64_t l = rt_value_as_int(left), r = rt_value_as_int(right);
    return rt_value_int(r == 0 || (l == INT64_MIN && r == -1) ? 0 : l % r);
}

#define ANY_ORDERED(name, op) \
int64_t name(int64_t left, int64_t right) { \
    if (rt_value_is_float(left) || rt_value_is_float(right)) \
        return any_as_f64(left) op any_as_f64(right); \
    return rt_value_as_int(left) op rt_value_as_int(right); \
}
ANY_ORDERED(rt_any_lt, <)
ANY_ORDERED(rt_any_gt, >)
ANY_ORDERED(rt_any_le, <=)
ANY_ORDERED(rt_any_ge, >=)
#undef ANY_ORDERED
