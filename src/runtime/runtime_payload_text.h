#ifndef SIMPLE_RUNTIME_PAYLOAD_TEXT_H
#define SIMPLE_RUNTIME_PAYLOAD_TEXT_H
#include <stddef.h>
#include <string.h>
/* dst has room for the host/GPU queue's 4096-byte payload text field. */
static void rt_host_gpu_queue_copy_payload_text(char* dst, const char* src) {
    if (!dst) return;
    if (!src) { dst[0] = '\0'; return; }
    size_t length = 0;
    while (length < 4095 && src[length]) ++length;
    memcpy(dst, src, length);
    dst[length] = '\0';
}
#endif
