#include <stdint.h>
#include <stdlib.h>
#include <string.h>

const char *rt_byte_char(int64_t value);
const char *rt_wire_to_hex(const char *wire, int64_t wire_len);
const char *rt_hex_to_wire(const char *hex);
int64_t rt_random_i64(void);

int main(void) {
    const char wire[] = {0x00, 0x7f, (char)0x80, (char)0xff};
    const char *byte = rt_byte_char(0x141);
    const char *hex = rt_wire_to_hex(wire, 4);
    const char *decoded = rt_hex_to_wire("007f80ff");
    const char *invalid = rt_hex_to_wire("0xz1");
    volatile int64_t random_value = rt_random_i64();
    (void)random_value;
    if (!byte || (unsigned char)byte[0] != 0x41 || byte[1] != '\0') return 1;
    if (!hex || strcmp(hex, "007f80ff") != 0) return 2;
    if (!decoded || memcmp(decoded, wire, sizeof(wire)) != 0 || decoded[4] != '\0') return 3;
    if (!invalid || invalid[0] != '\0') return 4;
    free((void *)byte);
    free((void *)hex);
    free((void *)decoded);
    free((void *)invalid);
    return 0;
}
