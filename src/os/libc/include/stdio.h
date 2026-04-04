/*
 * SimpleOS <stdio.h> — standard I/O definitions
 */

#ifndef _SIMPLEOS_STDIO_H
#define _SIMPLEOS_STDIO_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>
#include <stdarg.h>

#ifndef NULL
#define NULL ((void *)0)
#endif

#define EOF       (-1)
#define BUFSIZ    4096
#define FILENAME_MAX 256
#define FOPEN_MAX    256

#define SEEK_SET  0
#define SEEK_CUR  1
#define SEEK_END  2

/* Opaque FILE type */
typedef struct __simpleos_FILE FILE;

extern FILE *stdin;
extern FILE *stdout;
extern FILE *stderr;

/* Formatted output */
int printf(const char *fmt, ...);
int fprintf(FILE *stream, const char *fmt, ...);
int sprintf(char *str, const char *fmt, ...);
int snprintf(char *str, size_t size, const char *fmt, ...);
int vprintf(const char *fmt, va_list ap);
int vfprintf(FILE *stream, const char *fmt, va_list ap);
int vsprintf(char *str, const char *fmt, va_list ap);
int vsnprintf(char *str, size_t size, const char *fmt, va_list ap);

/* Formatted input */
int scanf(const char *fmt, ...);
int fscanf(FILE *stream, const char *fmt, ...);
int sscanf(const char *str, const char *fmt, ...);

/* Character / string I/O */
int   puts(const char *s);
int   fputs(const char *s, FILE *stream);
int   fputc(int c, FILE *stream);
int   putc(int c, FILE *stream);
int   putchar(int c);
int   fgetc(FILE *stream);
int   getc(FILE *stream);
int   getchar(void);
int   ungetc(int c, FILE *stream);
char *fgets(char *s, int size, FILE *stream);

/* File operations */
FILE  *fopen(const char *path, const char *mode);
FILE  *freopen(const char *path, const char *mode, FILE *stream);
int    fclose(FILE *stream);
size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);
size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);
int    fseek(FILE *stream, long offset, int whence);
long   ftell(FILE *stream);
void   rewind(FILE *stream);
int    fflush(FILE *stream);
int    feof(FILE *stream);
int    ferror(FILE *stream);
void   clearerr(FILE *stream);
int    fileno(FILE *stream);

/* File management */
int  remove(const char *path);
int  rename(const char *oldpath, const char *newpath);
FILE *tmpfile(void);
char *tmpnam(char *s);

/* POSIX-style low-level I/O (also in unistd.h) */
int     open(const char *path, int flags, ...);
ssize_t read(int fd, void *buf, size_t count);
ssize_t write(int fd, const void *buf, size_t count);
int     close(int fd);

/* Error printing */
void perror(const char *s);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_STDIO_H */
