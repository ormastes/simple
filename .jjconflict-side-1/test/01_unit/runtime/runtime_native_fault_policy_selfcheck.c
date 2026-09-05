#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void rt_fault_set_stack_overflow_detection(uint8_t enabled);
void rt_fault_set_max_recursion_depth(int64_t depth);
void rt_fault_set_timeout(int64_t secs);
void rt_fault_set_execution_limit(int64_t limit);

static int env_is(const char *name, const char *expected) {
    const char *actual = getenv(name);
    return actual != NULL && strcmp(actual, expected) == 0;
}

int main(void) {
    rt_fault_set_stack_overflow_detection(0);
    if (!env_is("SIMPLE_STACK_OVERFLOW_DETECTION", "0")) return 1;
    rt_fault_set_stack_overflow_detection(1);
    if (!env_is("SIMPLE_STACK_OVERFLOW_DETECTION", "1")) return 2;
    rt_fault_set_max_recursion_depth(2048);
    if (!env_is("SIMPLE_MAX_RECURSION_DEPTH", "2048")) return 3;
    rt_fault_set_timeout(0);
    if (!env_is("SIMPLE_TIMEOUT_SECONDS", "0")) return 4;
    rt_fault_set_timeout(37);
    if (!env_is("SIMPLE_TIMEOUT_SECONDS", "37")) return 5;
    rt_fault_set_execution_limit(987654);
    if (!env_is("SIMPLE_EXECUTION_LIMIT", "987654")) return 6;
    return 0;
}
