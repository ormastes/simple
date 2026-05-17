#include <ctype.h>
#include <stdint.h>

int32_t __is_alnum(int32_t ch) { return isalnum(ch); }
int32_t __is_alpha(int32_t ch) { return isalpha(ch); }
int32_t __is_digit(int32_t ch) { return isdigit(ch); }
int32_t __is_xdigit(int32_t ch) { return isxdigit(ch); }
int32_t __is_space(int32_t ch) { return isspace(ch); }
int32_t __is_lower(int32_t ch) { return islower(ch); }
int32_t __is_upper(int32_t ch) { return isupper(ch); }
