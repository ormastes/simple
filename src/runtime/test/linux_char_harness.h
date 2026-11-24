/* Minimal harness for Linux characterization selfchecks (no framework).
 * Each CHECK counts one assertion; DONE prints "<name>: P passed, F failed"
 * and returns non-zero on any failure. */
#ifndef LINUX_CHAR_HARNESS_H
#define LINUX_CHAR_HARNESS_H

#include <stdio.h>
#include <time.h>
#include <stdint.h>

static int g_char_pass, g_char_fail;

#define CHECK(c) do { if (c) g_char_pass++; else { g_char_fail++; \
    fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #c); } } while (0)
#define DONE(name) do { printf("%s: %d passed, %d failed\n", name, \
    g_char_pass, g_char_fail); return g_char_fail ? 1 : 0; } while (0)

static inline int64_t char_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* Lowest free fd: as an RLIMIT_NOFILE soft limit it leaves no free slot. */
#include <unistd.h>
static inline unsigned long char_first_free_fd(void) {
    int p = dup(0);
    if (p >= 0) close(p);
    return p < 0 ? 0 : (unsigned long)p;
}

#endif
