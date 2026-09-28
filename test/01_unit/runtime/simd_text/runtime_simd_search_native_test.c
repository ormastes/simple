/* Include the implementation first: this also checks its feature-test
 * macro ordering without help from the test or compiler command line. */
#include "runtime_simd_search.c"
#include <stdio.h>
#include <stdlib.h>

static unsigned checks;

static void check_search(const uint8_t* haystack, uint64_t hlen,
                         const uint8_t* needle, uint64_t nlen,
                         int64_t expected) {
    int64_t scalar = scalar_str_search_local(haystack, hlen, needle, nlen);
    int64_t selected = local_str_search(haystack, hlen, needle, nlen);
    if (scalar != expected || selected != expected) {
        fprintf(stderr, "search case %u: expected %lld, scalar %lld, selected %lld\n",
                checks, (long long)expected, (long long)scalar, (long long)selected);
        exit(1);
    }
    checks++;
}

int main(void) {
    const uint8_t text[] = "ababa";
    const uint8_t absent[] = "xyz";
    const uint8_t binary[] = {0xff, 0, 0x80, 0, 0xff, 0, 0x80};
    const uint8_t binary_needle[] = {0, 0x80};
    uint8_t haystack[96];
    const uint8_t needle[] = {0x80, 0, 0xff};
    local_dispatch_init();
    check_search(text, 0, text, 0, 0);
    check_search(text, 5, text, 0, 0);
    check_search(text, 0, text, 1, -1);
    check_search(text, 2, text, 3, -1);
    check_search(text, 5, text, 5, 0);
    check_search(text, 5, text, 3, 0);
    check_search(text, 5, text + 1, 3, 1);
    check_search(text, 5, text + 1, 1, 1);
    check_search(text, 5, absent, 1, -1);
    check_search(text, 5, absent, 3, -1);
    check_search(binary, sizeof(binary), binary_needle, sizeof(binary_needle), 1);
    check_search(binary, sizeof(binary), binary + 4, 3, 0);
    /* Every valid offset, including vector boundaries and the final byte. */
    for (size_t offset = 0; offset <= sizeof(haystack) - sizeof(needle); offset++) {
        memset(haystack, 0x41, sizeof(haystack));
        memcpy(haystack + offset, needle, sizeof(needle));
        check_search(haystack, sizeof(haystack), needle, sizeof(needle), (int64_t)offset);
        check_search(haystack, offset + sizeof(needle) - 1, needle, sizeof(needle), -1);
    }
    printf("PASS: %u scalar and selected SIMD search cases\n", checks);
    return 0;
}
