/* Host selfcheck for the x86_64 freestanding text accessors
 * (examples/09_embedded/simple_os/arch/x86_64/boot/x86_64_text_codepoint.h).
 * Bug x64_freestanding_char_code_at_dynamic_text: the freestanding
 * rt_string_char_code_at was BYTE-indexed and returned 0 for raw rodata
 * pointers, while the hosted runtime (runtime_native.c) is CODEPOINT-indexed
 * UTF-8 and accepts raw C strings. Build:
 *   clang -std=c11 -Wall -Werror -Iexamples/09_embedded/simple_os/arch/x86_64/boot \
 *     test/01_unit/runtime/x86_64_freestanding_char_code_at_test.c -o t && ./t */
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "x86_64_text_codepoint.h"

int main(void) {
    const unsigned char *ascii = (const unsigned char *)"hello";
    assert(x64_text_code_at(ascii, 5, 0) == 'h');
    assert(x64_text_code_at(ascii, 5, 4) == 'o');
    assert(x64_text_code_at(ascii, 5, 5) == 0);
    assert(x64_text_code_at(ascii, 5, -1) == 0);
    /* "café—x": é=U+00E9 (2B), —=U+2014 (3B), then x */
    const unsigned char *u = (const unsigned char *)"caf\xC3\xA9\xE2\x80\x94x\xF0\x9F\x98\x80";
    uint64_t ul = strlen((const char *)u);
    assert(x64_text_code_at(u, ul, 3) == 0xE9);
    assert(x64_text_code_at(u, ul, 4) == 0x2014);
    assert(x64_text_code_at(u, ul, 5) == 'x');
    assert(x64_text_code_at(u, ul, 6) == 0x1F600);
    assert(x64_text_code_at(u, ul, 7) == 0);
    /* byte_at stays byte-indexed */
    assert(x64_text_byte_at(u, ul, 3) == 0xC3);
    assert(x64_text_byte_at(u, ul, ul) == 0);
    /* raw NUL-terminated pointer length */
    assert(x64_text_cstr_len(u) == ul);
    printf("x86_64_freestanding_char_code_at_test: PASS\n");
    return 0;
}
