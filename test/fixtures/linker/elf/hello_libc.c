/* Dynamic-libc fixture: puts + exit through PLT, exit status 42. */
#include <stdio.h>
#include <stdlib.h>

int main(void) {
    puts("hi from libc");
    exit(42);
}
