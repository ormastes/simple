/* Focused behaviour check for the two SOSIX file-mapping operations as the
 * runtime owns them (runtime.c via the platform headers, and runtime_native.c):
 *
 *   ACTUAL access  : rt_mmap -> read the bytes through the view -> rt_munmap
 *   CACHING        : rt_mmap(readonly) -> rt_madvise(WILLNEED) -> rt_munmap
 *                    (the POSIX composition behind sosix_file_map_prefetch;
 *                    on Windows that op is a facade-level no-op and never
 *                    reaches these symbols, so this file is Unix-hosted)
 *
 * plus the bounds contract every owner must share: 0 for a region past the
 * end of the file, for an offset+size overflow, and for a missing path.
 * Runner: scripts/check/check-file-map-c.shs (compiles against BOTH owners). */
#include "../runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if !defined(_WIN32)
#include <stdlib.h>
#include <unistd.h>

#if defined(RT_FILE_MAP_SELFCHECK_STRING_SHIM)
/* runtime.c's owner (platform/unix_common.h) reads the path through the
 * tagged-string helpers that only runtime_native.c defines, and the two files
 * cannot be linked together here (both export the mmap family). Supply a
 * self-consistent shim: the owner never inspects the representation, only
 * calls these four. */
typedef struct { uint64_t len; uint8_t* data; } ShimString;
int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    ShimString* s = (ShimString*)malloc(sizeof(ShimString));
    if (!s) return 0;
    s->data = (uint8_t*)malloc(len ? len : 1);
    if (!s->data) { free(s); return 0; }
    memcpy(s->data, bytes, len);
    s->len = len;
    return (int64_t)(intptr_t)s;
}
int64_t rt_string_len(int64_t string) { return string ? (int64_t)((ShimString*)(intptr_t)string)->len : 0; }
const uint8_t* rt_string_data(int64_t string) { return string ? ((ShimString*)(intptr_t)string)->data : NULL; }
int64_t rt_string_free(int64_t string) {
    if (!string) return 0;
    free(((ShimString*)(intptr_t)string)->data);
    free((void*)(intptr_t)string);
    return 0;
}
#endif

static int check(int condition, const char* message) {
    if (condition) return 1;
    fprintf(stderr, "rt_file_map_selfcheck: %s\n", message);
    return 0;
}

int main(void) {
    /* File layout: one page of filler, then `payload` on the page boundary,
     * so the offset case maps at a legal (page-aligned) offset. */
    static const uint8_t payload[] = "sosix-file-map:\x00\x7f\x80\xff:end";
    const int64_t payload_len = (int64_t)sizeof(payload);
    long page = sysconf(_SC_PAGESIZE);
    if (!check(page > 0, "sysconf(_SC_PAGESIZE) failed")) return 1;
    const int64_t file_len = (int64_t)page + payload_len;
    char path[] = "/tmp/simple-file-map-XXXXXX";
    int fd = mkstemp(path);
    if (!check(fd >= 0, "mkstemp failed")) return 1;
    for (long i = 0; i < page; i++) {
        uint8_t filler = (uint8_t)(i & 0xff);
        if (!check(write(fd, &filler, 1) == 1, "filler write failed")) return 1;
    }
    if (!check(write(fd, payload, sizeof(payload)) == (ssize_t)sizeof(payload), "payload write failed")) return 1;
    if (!check(close(fd) == 0, "close failed")) return 1;
    int64_t tagged = rt_string_new((const uint8_t*)path, strlen(path));

    /* ACTUAL access: whole file, read-only, bytes visible through the view. */
    int64_t view = rt_mmap(tagged, file_len, 0, 1);
    if (!check(view > 0, "actual-read map failed")) return 1;
    if (!check(((const uint8_t*)(intptr_t)view)[1] == 1, "filler byte differs")) return 1;
    if (!check(memcmp((const uint8_t*)(intptr_t)view + page, payload, sizeof(payload)) == 0,
               "mapped bytes differ from the file")) return 1;
    if (!check(rt_munmap(view, file_len), "actual-read unmap failed")) return 1;

    /* ACTUAL access at a page-aligned offset: the view starts at payload[0]. */
    int64_t tail = rt_mmap(tagged, payload_len, (int64_t)page, 1);
    if (!check(tail > 0, "offset map failed")) return 1;
    if (!check(memcmp((const void*)(intptr_t)tail, payload, sizeof(payload)) == 0,
               "offset view bytes differ")) return 1;
    if (!check(rt_munmap(tail, payload_len), "offset unmap failed")) return 1;

    /* CACHING: read-only map, WILLNEED, release -- the prefetch composition. */
    int64_t warm = rt_mmap(tagged, file_len, 0, 1);
    if (!check(warm > 0, "prefetch map failed")) return 1;
    if (!check(rt_madvise(warm, file_len, 3), "prefetch madvise(WILLNEED) failed")) return 1;
    if (!check(rt_munmap(warm, file_len), "prefetch unmap failed")) return 1;

    /* Bounds contract: past end of file, overflow, size 0, missing path -> 0. */
    if (!check(rt_mmap(tagged, file_len + 1, 0, 1) == 0, "region past EOF was admitted")) return 1;
    if (!check(rt_mmap(tagged, payload_len + 1, (int64_t)page, 1) == 0, "offset+size past EOF was admitted")) return 1;
    if (!check(rt_mmap(tagged, INT64_MAX, INT64_MAX, 1) == 0, "offset+size overflow was admitted")) return 1;
    if (!check(rt_mmap(tagged, 0, 0, 1) == 0, "size 0 was admitted")) return 1;
    if (!check(!rt_munmap(0, payload_len), "unmap of address 0 succeeded")) return 1;
    rt_string_free(tagged);

    static const char missing[] = "/tmp/simple-file-map-does-not-exist";
    int64_t missing_tagged = rt_string_new((const uint8_t*)missing, sizeof(missing) - 1U);
    if (!check(rt_mmap(missing_tagged, 16, 0, 1) == 0, "missing file was mapped")) return 1;
    rt_string_free(missing_tagged);

    unlink(path);
    puts("PASS: rt_file_map actual-read + prefetch + bounds contract");
    return 0;
}
#else
int main(void) {
    puts("SKIP: rt_file_map selfcheck is Unix-hosted (Windows prefetch is a facade no-op)");
    return 0;
}
#endif
