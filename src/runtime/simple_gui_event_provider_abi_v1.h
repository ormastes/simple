#ifndef SIMPLE_GUI_EVENT_PROVIDER_ABI_V1_H
#define SIMPLE_GUI_EVENT_PROVIDER_ABI_V1_H

#include <stdint.h>

#define SIMPLE_GUI_EVENT_PROVIDER_ABI_VERSION_V1 1
#define SIMPLE_GUI_EVENT_PACKET_CAPACITY_V1 4096
#define SIMPLE_GUI_EVENT_WAIT_MS_V1 16

#ifdef __cplusplus
extern "C" {
#endif

/* Optional extension on the HTML v1 library. Session calls are macOS-main-
 * thread-only and MUST NOT reenter runtime GUI entrypoints. Poll borrows the
 * buffer only during its call. Return 0 after an idle wait, -1 on failure, or
 * the packet byte length. Packet: 1..31 lowercase ASCII/hyphen kind bytes,
 * '\n', UTF-8 payload (which may contain '\n'); no embedded NUL. Do not write
 * beyond capacity. Pump AppKit while waiting up to wait_ms. Bound the provider
 * queue and preserve close events. Shutdown returns 1 on success and any
 * other value on failure. It releases session UI resources;
 * the library itself remains loaded. A later present starts a new session.
 * Standalone HTML calls must not overlap an event session. */
int64_t simple_gui_event_provider_abi_v1(void);
int64_t simple_gui_poll_event_v1(uint8_t *bytes, uint64_t capacity,
                                uint64_t wait_ms);
int64_t simple_gui_shutdown_v1(void);

#ifdef __cplusplus
}
#endif
#endif
