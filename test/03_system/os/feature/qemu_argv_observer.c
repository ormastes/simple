#include <stdio.h>

/* Host-process fixture: observe argv, stderr, and exit propagation only. */
int main(int argc, char **argv) {
    for (int index = 1; index < argc; ++index) {
        printf("arg[%d]=%s\n", index - 1, argv[index]);
    }
    fputs("argv-observer: invoked\n", stderr);
    return 37;
}
