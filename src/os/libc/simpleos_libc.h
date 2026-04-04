/*
 * SimpleOS Libc Shim — minimal C runtime for toolchain porting
 *
 * Provides: memory allocation, string ops, basic I/O, errno
 * Delegates to SimpleOS syscalls via inline assembly (x86_64 SYSCALL).
 *
 * Syscall ABI (from src/os/userlib/syscall_raw.spl):
 *   rax = id, rdi = arg0, rsi = arg1, rdx = arg2, r10 = arg3, r8 = arg4
 *   result in rax
 *
 * Freestanding — only uses compiler-provided headers (stddef, stdint, stdarg).
 */

#ifndef SIMPLEOS_LIBC_H
#define SIMPLEOS_LIBC_H

#include <stddef.h>
#include <stdint.h>
#include <stdarg.h>

/* ---- types ------------------------------------------------------------ */

typedef int64_t  ssize_t;
typedef int64_t  off_t;

/* ---- errno ------------------------------------------------------------ */

extern int errno;

#define ENOENT   2
#define EIO      5
#define EBADF    9
#define ENOMEM  12
#define EACCES  13
#define EFAULT  14
#define EEXIST  17
#define ENOTDIR 20
#define EINVAL  22
#define ENOSYS  38

/* ---- memory allocation ------------------------------------------------ */

void *malloc(size_t size);
void  free(void *ptr);
void *calloc(size_t nmemb, size_t size);
void *realloc(void *ptr, size_t size);

/* ---- mmap / munmap ---------------------------------------------------- */

#define PROT_READ   0x1
#define PROT_WRITE  0x2
#define PROT_EXEC   0x4
#define MAP_PRIVATE   0x02
#define MAP_ANONYMOUS 0x20
#define MAP_FAILED  ((void *)-1)

void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
int   munmap(void *addr, size_t length);

/* ---- string operations ------------------------------------------------ */

size_t strlen(const char *s);
char  *strcpy(char *dest, const char *src);
char  *strncpy(char *dest, const char *src, size_t n);
int    strcmp(const char *s1, const char *s2);
int    strncmp(const char *s1, const char *s2, size_t n);
char  *strcat(char *dest, const char *src);
char  *strchr(const char *s, int c);
char  *strrchr(const char *s, int c);
char  *strstr(const char *haystack, const char *needle);
char  *strdup(const char *s);

/* ---- memory operations ------------------------------------------------ */

void *memcpy(void *dest, const void *src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
void *memset(void *s, int c, size_t n);
int   memcmp(const void *s1, const void *s2, size_t n);

/* ---- I/O -------------------------------------------------------------- */

typedef struct simpleos_FILE FILE;

extern FILE *stdin;
extern FILE *stdout;
extern FILE *stderr;

int printf(const char *fmt, ...);
int fprintf(FILE *stream, const char *fmt, ...);
int snprintf(char *str, size_t size, const char *fmt, ...);
int vsnprintf(char *str, size_t size, const char *fmt, va_list ap);
int puts(const char *s);
int fputs(const char *s, FILE *stream);
int fputc(int c, FILE *stream);

/* POSIX-style file I/O */
int     open(const char *path, int flags, ...);
ssize_t read(int fd, void *buf, size_t count);
ssize_t write(int fd, const void *buf, size_t count);
int     close(int fd);

/* ---- process ---------------------------------------------------------- */

void exit(int status) __attribute__((noreturn));
void abort(void) __attribute__((noreturn));
int  getpid(void);

/* ---- math (basic) ----------------------------------------------------- */

double fabs(double x);
double sqrt(double x);
float  fabsf(float x);
float  sqrtf(float x);

/* ---- environment (stubs) ---------------------------------------------- */

char *getenv(const char *name);
int   setenv(const char *name, const char *value, int overwrite);

/* ---- time (stub) ------------------------------------------------------ */

typedef long time_t;
time_t time(time_t *tloc);

#endif /* SIMPLEOS_LIBC_H */
