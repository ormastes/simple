#ifndef SIMPLE_RUNTIME_CAPTURE_SPLICE_PRIVATE_H
#define SIMPLE_RUNTIME_CAPTURE_SPLICE_PRIVATE_H
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Shared by the POSIX fork capture (runtime_fork.c) and the Windows capture
 * (runtime_process.c). Both keep `head_len` head bytes at `data` and the
 * ordered tail at `tail`; this joins them, inserting the truncation marker when
 * `total` exceeds what was kept.
 * Returns the joined length (head + marker + tail); the caller writes the
 * terminating NUL. */
static inline size_t rt_capture_splice_tail(char* data, size_t head_len, char* tail,
                                            size_t tail_len, uint64_t total) {
    size_t marker_len = 0;
    if (total > head_len + tail_len) {
        char marker[96];
        uint64_t omitted = total - head_len - tail_len;
        int written = snprintf(marker, sizeof(marker), "\n[output truncated: %llu bytes omitted]\n",
                               (unsigned long long)omitted);
        if (written > 0) marker_len = (size_t)written;
        memmove(data + head_len + marker_len, tail, tail_len);
        memcpy(data + head_len, marker, marker_len);
    } else {
        memmove(data + head_len, tail, tail_len);
    }
    return head_len + marker_len + tail_len;
}
#endif
