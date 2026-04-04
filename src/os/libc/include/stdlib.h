/*
 * SimpleOS <stdlib.h> — general utilities
 */

#ifndef _SIMPLEOS_STDLIB_H
#define _SIMPLEOS_STDLIB_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

#ifndef NULL
#define NULL ((void *)0)
#endif

#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1
#define RAND_MAX     2147483647

/* Memory allocation */
void *malloc(size_t size);
void  free(void *ptr);
void *calloc(size_t nmemb, size_t size);
void *realloc(void *ptr, size_t size);
int   posix_memalign(void **memptr, size_t alignment, size_t size);
void *aligned_alloc(size_t alignment, size_t size);
void *memalign(size_t alignment, size_t size);

/* Process control */
void exit(int status) __attribute__((noreturn));
void abort(void) __attribute__((noreturn));
void _Exit(int status) __attribute__((noreturn));
int  atexit(void (*func)(void));

/* String conversion */
int       atoi(const char *nptr);
long      atol(const char *nptr);
long long atoll(const char *nptr);
long      strtol(const char *nptr, char **endptr, int base);
unsigned long strtoul(const char *nptr, char **endptr, int base);
long long strtoll(const char *nptr, char **endptr, int base);
unsigned long long strtoull(const char *nptr, char **endptr, int base);
double    strtod(const char *nptr, char **endptr);
float     strtof(const char *nptr, char **endptr);

/* Environment */
char *getenv(const char *name);
int   setenv(const char *name, const char *value, int overwrite);
int   unsetenv(const char *name);
int   system(const char *command);

/* Integer arithmetic */
int       abs(int j);
long      labs(long j);
long long llabs(long long j);

typedef struct {
    int quot;
    int rem;
} div_t;

typedef struct {
    long quot;
    long rem;
} ldiv_t;

typedef struct {
    long long quot;
    long long rem;
} lldiv_t;

div_t   div(int numer, int denom);
ldiv_t  ldiv(long numer, long denom);
lldiv_t lldiv(long long numer, long long denom);

/* Searching and sorting */
void *bsearch(const void *key, const void *base, size_t nmemb,
              size_t size, int (*compar)(const void *, const void *));
void  qsort(void *base, size_t nmemb, size_t size,
             int (*compar)(const void *, const void *));

/* Pseudo-random numbers */
int  rand(void);
void srand(unsigned int seed);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_STDLIB_H */
