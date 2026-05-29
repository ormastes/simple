#include <stdatomic.h>
#include <stdbool.h>

static atomic_bool g_macro_trace_enabled = false;
static atomic_bool g_debug_mode_enabled = false;

void rt_set_macro_trace(bool enabled) {
    atomic_store_explicit(&g_macro_trace_enabled, enabled, memory_order_seq_cst);
}

bool rt_is_macro_trace_enabled(void) {
    return atomic_load_explicit(&g_macro_trace_enabled, memory_order_seq_cst);
}

void rt_set_debug_mode(bool enabled) {
    atomic_store_explicit(&g_debug_mode_enabled, enabled, memory_order_seq_cst);
}

bool rt_is_debug_mode_enabled(void) {
    return atomic_load_explicit(&g_debug_mode_enabled, memory_order_seq_cst);
}
