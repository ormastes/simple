#include <stdint.h>
#include <stdlib.h>
#include <string.h>

const char *rt_random_hex(int64_t length);

static int is_lower_hex(const char *value) {
    for (const char *cursor = value; *cursor; cursor++) {
        if (!((*cursor >= '0' && *cursor <= '9') ||
              (*cursor >= 'a' && *cursor <= 'f'))) return 0;
    }
    return 1;
}

int main(void) {
    const char *empty = rt_random_hex(0);
    const char *one = rt_random_hex(1);
    const char *sixteen = rt_random_hex(16);
    const char *invalid = rt_random_hex(-1);
    if (!empty || strcmp(empty, "") != 0) return 1;
    if (!one || strlen(one) != 2 || !is_lower_hex(one)) return 2;
    if (!sixteen || strlen(sixteen) != 32 || !is_lower_hex(sixteen)) return 3;
    if (invalid != NULL) return 4;
    free((void *)empty);
    free((void *)one);
    free((void *)sixteen);
    return 0;
}
