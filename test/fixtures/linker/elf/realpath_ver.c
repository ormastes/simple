#include <stdlib.h>
#include <stdio.h>
int main(void){ char *p = realpath("/", NULL); printf("realpath=%s\n", p ? p : "NULL"); return p ? 42 : 7; }
