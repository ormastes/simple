#include <stdio.h>
#ifdef FEATURE_A
int mode = 1;
#else
int mode = 0;
#endif
int main(void) { return mode; }
