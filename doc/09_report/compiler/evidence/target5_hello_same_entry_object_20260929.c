#include <stdint.h>
#include <stdio.h>

// Replaces only the Simple hello module in the captured LLD response.
// The archived Simple entry, runtime, CRT, libraries, and linker flags remain.
int64_t __simple_main(void) {
    puts("Hello World");
    return 0;
}
