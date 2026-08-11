#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include "runtime.h"

bool rt_terminal_disable_raw_mode(void) { return true; }
void rt_terminal_signal_scope_emergency_restore(void) {}

int main(int argc, char** argv) {
    const uint8_t function_name[] = "provider_probe";
    const int64_t condition = argc > 1 && strcmp(argv[1], "fail") == 0 ? 0 : 1;
    simple_contract_check(condition, 5, function_name, 14);
    return 0;
}
