#ifndef SHIM_STRING_H
#define SHIM_STRING_H
#include <stddef.h>
size_t strlen(const char *);
int strcmp(const char *, const char *);
char *strchr(const char *, int);
void *memcpy(void *, const void *, size_t);
char *strerror(int);
#endif
