#include <stdint.h>

extern void rt_println_str(const uint8_t *, uint64_t);

// Replaces only the Simple hello module in the captured LLD response.
// The archived Simple entry, runtime, CRT, libraries, and linker flags remain.
int64_t __simple_main(void) {
    static const uint8_t message[] = "Hello World";
    rt_println_str(message, sizeof(message) - 1);
    return 0;
}
