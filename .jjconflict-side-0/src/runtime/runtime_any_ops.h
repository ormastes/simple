#ifndef SIMPLE_RUNTIME_ANY_OPS_H
#define SIMPLE_RUNTIME_ANY_OPS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

int64_t rt_any_sub(int64_t left, int64_t right);
int64_t rt_any_mul(int64_t left, int64_t right);
int64_t rt_any_div(int64_t left, int64_t right);
int64_t rt_any_mod(int64_t left, int64_t right);
int64_t rt_any_lt(int64_t left, int64_t right);
int64_t rt_any_gt(int64_t left, int64_t right);
int64_t rt_any_le(int64_t left, int64_t right);
int64_t rt_any_ge(int64_t left, int64_t right);

#ifdef __cplusplus
}
#endif

#endif
