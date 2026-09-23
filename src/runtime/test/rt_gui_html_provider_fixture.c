#include "simple_gui_html_provider_abi_v1.h"

#include <stdatomic.h>
#include <string.h>

#ifndef SIMPLE_GUI_TEST_ABI_VERSION
#define SIMPLE_GUI_TEST_ABI_VERSION SIMPLE_GUI_HTML_PROVIDER_ABI_VERSION_V1
#endif

static atomic_int version_calls = ATOMIC_VAR_INIT(0);
static atomic_int present_calls = ATOMIC_VAR_INIT(0);

int64_t simple_gui_html_provider_abi_v1(void) {
    atomic_fetch_add_explicit(&version_calls, 1, memory_order_relaxed);
    return SIMPLE_GUI_TEST_ABI_VERSION;
}

int64_t simple_gui_present_html_v1(const uint8_t *utf8, uint64_t length) {
#if defined(SIMPLE_GUI_TEST_REJECT_FRAME)
    (void)utf8;
    (void)length;
    return 0;
#else
    if (!utf8 || length != 9 || memcmp(utf8, "<p>ok</p>", 9) != 0) return 0;
    atomic_fetch_add_explicit(&present_calls, 1, memory_order_relaxed);
    return 1;
#endif
}

int64_t simple_gui_test_call_counts_v1(void) {
    return 100 * atomic_load_explicit(&version_calls, memory_order_relaxed) +
           atomic_load_explicit(&present_calls, memory_order_relaxed);
}
