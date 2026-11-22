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

static inline void rt_capture_reverse_bytes(char* data, size_t len) {
    for (size_t left = 0, right = len ? len - 1 : 0; left < right; left++, right--) {
        char tmp = data[left];
        data[left] = data[right];
        data[right] = tmp;
    }
}

/* Head-then-ring-tail append of `len` bytes: fill the head up to `head_limit`,
 * then keep the newest `tail_limit` bytes in the ring at `tail`. */
static inline void rt_capture_ring_append(char* data, size_t* head_len, size_t head_limit,
                                          char* tail, size_t tail_limit,
                                          size_t* tail_start, size_t* tail_len,
                                          const char* bytes, size_t len) {
    size_t head_add = head_limit - *head_len;
    if (head_add > len) head_add = len;
    memcpy(data + *head_len, bytes, head_add);
    *head_len += head_add;
    bytes += head_add;
    len -= head_add;
    if (len == 0 || tail_limit == 0) return;

    if (len >= tail_limit) {
        memcpy(tail, bytes + len - tail_limit, tail_limit);
        *tail_start = 0;
        *tail_len = tail_limit;
        return;
    }
    size_t overflow = *tail_len + len > tail_limit ? *tail_len + len - tail_limit : 0;
    *tail_start = (*tail_start + overflow) % tail_limit;
    *tail_len -= overflow;
    size_t write_at = (*tail_start + *tail_len) % tail_limit;
    size_t first = tail_limit - write_at;
    if (first > len) first = len;
    memcpy(tail + write_at, bytes, first);
    memcpy(tail, bytes + first, len - first);
    *tail_len += len;
}
#endif
