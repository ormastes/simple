/* Real hosted/native provider-pair regression; no mock text or array owner. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t rt_bytes_to_text(int64_t bytes_value);

static int check(const uint8_t *source, size_t length, int code) {
    int64_t text = rt_string_new(source, length);
    int64_t bytes = rt_text_to_bytes(text);
    if (rt_array_len_safe(bytes) != (int64_t)length) return code;
    const uint8_t *actual = (const uint8_t *)(uintptr_t)
        rt_array_data_ptr((SplArray *)(uintptr_t)bytes);
    if (length && (!actual || memcmp(actual, source, length))) return code + 1;
    int64_t roundtrip = rt_bytes_to_text(bytes);
    if (rt_string_len(roundtrip) != (int64_t)length) return code + 2;
    if (length && memcmp(rt_string_data(roundtrip), source, length)) return code + 3;
    return 0;
}

int main(void) {
    static const uint8_t ascii[] = {'p', 'k', 'g'};
    static const uint8_t nul[] = {'a', 0, 'b'};
    static const uint8_t unicode[] = {0xc3, 0xa9, 0xf0, 0x9f, 0x98, 0x80};
    int status = check(ascii, sizeof(ascii), 11);
    if (!status) status = check(nul, sizeof(nul), 21);
    if (!status) status = check(unicode, sizeof(unicode), 31);
    if (!status) status = check((const uint8_t *)"", 0, 41);
    if (status) return status;
    puts("PASS: hosted text/bytes ABI ASCII, embedded NUL, UTF-8, empty and roundtrip");
    return 0;
}
