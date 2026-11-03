/* stdin_read_char must use raw fd reads, not buffered stdio fgetc: fgetc
 * read-ahead swallows bytes that other raw read(0) users expect, and hung on
 * macOS ARM64 core-c. Build (the real function is extracted from
 * runtime_native.c so this tests the shipped source):
 *   sed -n '/^int64_t stdin_read_char(void) {/,/^}/p' ../runtime_native.c > fn.inc
 *   clang -DFN_INC='"fn.inc"' rt_stdin_read_char_raw_selfcheck.c -o sc
 *   printf 'ABCDEF' | ./sc
 * Expect: 'A' via stdin_read_char, then raw read gets "BCDEF", then EOF "". */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#if defined(_WIN32)
#include <io.h>
#include <fcntl.h>
#define RAW_READ(b, n) _read(0, (b), (unsigned)(n))
#else
#include <unistd.h>
#define RAW_READ(b, n) read(0, (b), (n))
#endif
#ifndef FN_INC
#define FN_INC "fn.inc"
#endif

static char g_last[4];
static int64_t g_len;
int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    g_len = (int64_t)len;
    if (len == 1) g_last[0] = (char)bytes[0];
    return g_len;
}
#include FN_INC

int main(void) {
#if defined(_WIN32)
    _setmode(0, _O_BINARY);
#endif
    if (stdin_read_char() != 1 || g_last[0] != 'A') { puts("FAIL first char"); return 1; }
    char rest[8] = {0};
    int n = (int)RAW_READ(rest, 5);
    if (n != 5 || memcmp(rest, "BCDEF", 5) != 0) {
        printf("FAIL mixed raw read saw %d bytes (stdio read-ahead swallowed input)\n", n);
        return 2;
    }
    if (stdin_read_char() != 0) { puts("FAIL EOF should be empty string"); return 3; }
    puts("PASS");
    return 0;
}
