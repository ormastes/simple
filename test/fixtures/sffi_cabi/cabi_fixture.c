/* Real C ABI fixture for RB-SFFI-04. Compile with clang only. */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

typedef enum { COLOR_RED = 0, COLOR_GREEN = 1, COLOR_BLUE = 2 } color_t;

int fx_int(void) { return -7; }
int32_t fx_int32(void) { return 2147483647; }
bool fx_bool(void) { return true; }
color_t fx_enum(void) { return COLOR_BLUE; }
/* Borrowed: static storage, the caller frees nothing. */
const char *fx_cstr(void) { return "borrowed-text"; }
const char *fx_cstr_null(void) { return NULL; }

int main(void) {
    printf("sizeof int=%zu\n", sizeof(int));
    printf("sizeof int32_t=%zu\n", sizeof(int32_t));
    printf("sizeof bool=%zu\n", sizeof(bool));
    printf("sizeof enum=%zu\n", sizeof(color_t));
    printf("int=%d\n", fx_int());
    printf("int32=%d\n", (int)fx_int32());
    printf("bool=%d\n", (int)fx_bool());
    printf("enum=%d\n", (int)fx_enum());
    printf("cstr=%s\n", fx_cstr());
    printf("cstr_null=%d\n", fx_cstr_null() == NULL);
    return 0;
}
