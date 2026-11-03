/* All four stdin readers must share one raw fd byte reader: stdio read-ahead
 * in any of them swallows bytes the others (or raw read(0) users) expect.
 * Build (real functions are extracted from runtime_native.c):
 *   R=../runtime_native.c; : > fn.inc
 *   sed -n '/^static int stdin_raw_byte(/,/^}/p' $R >> fn.inc
 *   for f in rt_read_stdin_line rt_stdin_read_line_text rt_stdin_read_chars_text stdin_read_char; do
 *     sed -n "/^int64_t $f(/,/^}/p" $R >> fn.inc; done
 *   clang -DFN_INC='"fn.inc"' rt_stdin_read_char_raw_selfcheck.c -o sc
 *   printf 'line1\nABCDEFGHIJ' | ./sc
 * Expect: line "line1", char 'A', 3 chars "BCD", raw read "EFGH", EOF. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#if defined(_WIN32)
#include <io.h>
#include <fcntl.h>
#define RAW_READ(b, n) _read(0, (b), (unsigned)(n))
#else
#include <unistd.h>
#include <sys/types.h>
#define RAW_READ(b, n) read(0, (b), (n))
#endif
#ifndef FN_INC
#define FN_INC "fn.inc"
#endif

static char g_last[64];
static int64_t g_len;
int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    g_len = (int64_t)len;
    if (len < sizeof(g_last)) { if (len) memcpy(g_last, bytes, len); g_last[len] = 0; }
    return g_len;
}
void *rt_observed_realloc_v1(void *p, size_t n) { return realloc(p, n); }
void *rt_observed_malloc_v1(size_t n) { return malloc(n); }
int64_t splc_utf8_valid_up_to(const uint8_t *b, int64_t n) { (void)b; return n; }
#include FN_INC

int main(void) {
#if defined(_WIN32)
    _setmode(0, _O_BINARY);
#endif
    rt_read_stdin_line();
    if (strcmp(g_last, "line1") != 0) { printf("FAIL line '%s'\n", g_last); return 1; }
    if (stdin_read_char() != 1 || g_last[0] != 'A') { puts("FAIL char after line"); return 2; }
    rt_stdin_read_chars_text(3);
    if (g_len != 3 || strcmp(g_last, "BCD") != 0) { printf("FAIL chars '%s'\n", g_last); return 3; }
    char rest[8] = {0};
    int n = (int)RAW_READ(rest, 4);
    if (n != 4 || memcmp(rest, "EFGH", 4) != 0) {
        printf("FAIL mixed raw read saw %d bytes (stdio read-ahead swallowed input)\n", n);
        return 4;
    }
    rt_stdin_read_chars_text(10);
    if (g_len != 2 || strcmp(g_last, "IJ") != 0) { printf("FAIL short chars '%s'\n", g_last); return 5; }
    if (stdin_read_char() != 0) { puts("FAIL EOF should be empty string"); return 6; }
    puts("PASS");
    return 0;
}
