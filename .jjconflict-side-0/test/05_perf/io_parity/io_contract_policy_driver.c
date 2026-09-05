#include <stdio.h>

int io_contract_ok(int open_ok, int missing_rejected, long partial_len,
                   long eof_len, int exact_ok, int exact_short_rejected);

int main(void) {
    int failures = 0;
    failures += !io_contract_ok(1, 1, 11, 0, 1, 1);
    failures += io_contract_ok(0, 1, 11, 0, 1, 1);
    failures += io_contract_ok(1, 0, 11, 0, 1, 1);
    failures += io_contract_ok(1, 1, 10, 0, 1, 1);
    failures += io_contract_ok(1, 1, 11, 1, 1, 1);
    failures += io_contract_ok(1, 1, 11, 0, 0, 1);
    failures += io_contract_ok(1, 1, 11, 0, 1, 0);
    if (failures != 0) {
        fprintf(stderr, "io-contract-policy failures=%d\n", failures);
        return 1;
    }
    puts("io-contract-policy decisions=1 conditions=6 status=pass");
    return 0;
}
