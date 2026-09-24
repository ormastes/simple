#ifndef SIMPLE_GUI_HTML_PROVIDER_ABI_V1_H
#define SIMPLE_GUI_HTML_PROVIDER_ABI_V1_H

#include <stdint.h>

#define SIMPLE_GUI_HTML_PROVIDER_ABI_VERSION_V1 1

#ifdef __cplusplus
extern "C" {
#endif

/* Export both symbols from the optional GUI library. The version callback is
 * called once under the runtime's initialization lock and MUST NOT reenter
 * rt_gui_present_html. Present calls can arrive concurrently; the provider
 * must serialize or route them to its GUI thread as appropriate. UTF-8 bytes
 * are borrowed for each synchronous call only: do not retain or modify them.
 * A present call returns 1 only after the frame was accepted. */
int64_t simple_gui_html_provider_abi_v1(void);
int64_t simple_gui_present_html_v1(const uint8_t *utf8, uint64_t length);

#ifdef __cplusplus
}
#endif

#endif
