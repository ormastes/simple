/* Explicit symbol version: .symver binds to a NON-default version, which this
   linker does not support (it binds each reference to the library default). */
#include <stdio.h>
#include <stdlib.h>
__asm__(".symver realpath, realpath@GLIBC_2.2.5");
int main(void) { char *p = realpath("/", NULL); printf("symver=%s\n", p ? p : "NULL"); return 42; }
