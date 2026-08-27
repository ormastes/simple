#include <stddef.h>

int io_contract_ok(int open_ok, int missing_rejected, long partial_len,
                   long eof_len, int exact_ok, int exact_short_rejected) {
    return open_ok && missing_rejected && partial_len == 11 && eof_len == 0 &&
           exact_ok && exact_short_rejected;
}
