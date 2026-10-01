/* Link against the production runtime_native.c, not a replacement concat. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t rt_string_new(const uint8_t*, uint64_t);
extern int64_t rt_string_len(int64_t);
extern const uint8_t* rt_string_data(int64_t);
extern int64_t rt_strcat_tagged(int64_t, int64_t);
extern int64_t rt_value_nil(void);

static int check(const char* label, int64_t left, int64_t right,
                 const uint8_t* expected, size_t length) {
    int64_t result = rt_strcat_tagged(left, right);
    int64_t actual_length = rt_string_len(result);
    const uint8_t* bytes = rt_string_data(result);
    if (actual_length != (int64_t)length || !bytes ||
            memcmp(bytes, expected, length) != 0 || bytes[length] != 0) {
        fprintf(stderr, "FAIL %s: actual length=%lld expected=%zu\n",
                label, (long long)actual_length, length);
        return 1;
    }
    return 0;
}

int main(void) {
    static const uint8_t with_nul[] = {'A', 0, 'B'};
    static const uint8_t pair[] = {'A', 0, 'B', 'A', 0, 'B'};
    static const uint8_t raw_then_nul[] = {'X', 'A', 0, 'B'};
    static const uint8_t nul_then_raw[] = {'A', 0, 'B', 'Y'};
    static const uint8_t nul_byte[] = {0};
    static const uint8_t two_nuls[] = {0, 0};
    static const uint8_t plain[] = {'X', 'Y'};
    static const uint8_t empty[] = {0};
    int64_t tagged = rt_string_new(with_nul, sizeof(with_nul));
    int64_t nul = rt_string_new(nul_byte, sizeof(nul_byte));
    int64_t blank = rt_string_new(empty, 0);
    int64_t raw_x = (int64_t)(uintptr_t)"X";
    int64_t raw_y = (int64_t)(uintptr_t)"Y";
    int failures = 0;
    failures += check("tagged NUL both operands", tagged, tagged, pair, sizeof(pair));
    failures += check("raw left tagged right", raw_x, tagged, raw_then_nul, sizeof(raw_then_nul));
    failures += check("tagged left raw right", tagged, raw_y, nul_then_raw, sizeof(nul_then_raw));
    failures += check("only NUL", nul, nul, two_nuls, sizeof(two_nuls));
    failures += check("tagged empty left", blank, tagged, with_nul, sizeof(with_nul));
    failures += check("tagged empty right", tagged, blank, with_nul, sizeof(with_nul));
    failures += check("raw operands", raw_x, raw_y, plain, sizeof(plain));
    failures += check("nil left", rt_value_nil(), tagged, with_nul, sizeof(with_nul));
    failures += check("nil right", tagged, rt_value_nil(), with_nul, sizeof(with_nul));
    failures += check("null and low-value fallback", 0, 7, empty, 0);
    if (failures) return 1;
    puts("RUNTIME_CONCAT_NUL_PASS checks=10");
    return 0;
}
