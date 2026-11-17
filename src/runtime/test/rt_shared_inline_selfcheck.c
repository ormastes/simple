/* Selfcheck for the shared static-inline bodies in runtime.h (hex, FNV-1a
 * string hash, secure-temp diag text) and platform.h (dir-list free, tagged
 * text data). Header-only: no runtime link needed.
 * clang -std=gnu11 -O1 -o /tmp/rt_shared_inline src/runtime/test/rt_shared_inline_selfcheck.c */
#include "../runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int64_t rt_string_len(int64_t s) { (void)s; return 0; }
const uint8_t* rt_string_data(int64_t s) { (void)s; return NULL; }
static int fails;
#define CHECK(c) do { if (!(c)) { printf("FAIL line %d: %s\n", __LINE__, #c); fails++; } } while (0)

int main(void) {
    CHECK(rt__shared_hex_digit_value('0') == 0 && rt__shared_hex_digit_value('9') == 9);
    CHECK(rt__shared_hex_digit_value('a') == 10 && rt__shared_hex_digit_value('F') == 15);
    CHECK(rt__shared_hex_digit_value('g') == -1 && rt__shared_hex_digit_value(' ') == -1);

    uint8_t bin[4];
    CHECK(rt__shared_hex_decode_into("00ffA5b6", 4, bin) == 0);
    CHECK(bin[0] == 0x00 && bin[1] == 0xff && bin[2] == 0xa5 && bin[3] == 0xb6);
    CHECK(rt__shared_hex_decode_into("00zz", 2, bin) == -1);

    char hex[9];
    rt__shared_hex_encode_into(bin, 4, hex);
    CHECK(strcmp(hex, "00ffa5b6") == 0);

    /* FNV-1a 64 */
    CHECK(rt__shared_str_hash(NULL) == 14695981039346656037ULL);
    CHECK(rt__shared_str_hash("") == 14695981039346656037ULL);
    CHECK(rt__shared_str_hash("a") == 0xaf63dc4c8601ec8cULL);
    CHECK(rt__shared_str_hash("foobar") == 0x85944171f73967e8ULL);

    const char** list = (const char**)malloc(3 * sizeof(char*));
    list[0] = (char*)malloc(2); list[1] = (char*)malloc(2); list[2] = NULL;
    rt__shared_dir_list_free(list, 2);
    rt__shared_dir_list_free(NULL, 0);

    int64_t n = -1;
    const char* big = "hello";
    CHECK(rt__shared_file_text_at_string_data(0, &n) == NULL && n == 0);
    CHECK(rt__shared_file_text_at_string_data((int64_t)(uintptr_t)big, &n) == big && n == 5);

    printf(fails ? "rt_shared_inline_selfcheck FAIL\n" : "rt_shared_inline_selfcheck PASS\n");
    return fails != 0;
}
