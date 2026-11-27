#ifndef SHIM_STDIO_H
#define SHIM_STDIO_H
typedef struct shim_FILE FILE;
extern FILE *stdout, *stderr;
int printf(const char *, ...);
int fprintf(FILE *, const char *, ...);
int fputs(const char *, FILE *);
int puts(const char *);
int fflush(FILE *);
#endif
