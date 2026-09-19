#include <stdio.h>
static int impl(void){ return 42; }
static void *resolver(void){ return (void*)impl; }
int f(void) __attribute__((ifunc("resolver")));
int main(void){ int r = f(); printf("f=%d\n", r); return r; }
