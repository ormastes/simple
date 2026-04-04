/*
 * SimpleOS Libc Shim — Extended string and memory-search functions
 *
 * strerror, strncat, strspn/strcspn, strtok/strtok_r,
 * strndup, strnlen, memchr, strcasecmp/strncasecmp.
 *
 * These complement the core functions already in simpleos_libc.c
 * (strlen, strcpy, strncpy, strcmp, strncmp, strcat, strchr, strrchr,
 *  strstr, strdup, memcpy, memmove, memset, memcmp).
 */

#include "include/string.h"
#include "include/stdlib.h"
#include "include/errno.h"

extern int errno;

/* ====================================================================
 * 1. strerror — human-readable error descriptions
 * ==================================================================== */

char *strerror(int errnum) {
    switch (errnum) {
    case  0: return "Success";
    case  1: return "Operation not permitted";
    case  2: return "No such file or directory";
    case  3: return "No such process";
    case  4: return "Interrupted system call";
    case  5: return "I/O error";
    case  6: return "No such device or address";
    case  7: return "Argument list too long";
    case  8: return "Exec format error";
    case  9: return "Bad file descriptor";
    case 10: return "No child processes";
    case 11: return "Resource temporarily unavailable";
    case 12: return "Cannot allocate memory";
    case 13: return "Permission denied";
    case 14: return "Bad address";
    case 16: return "Device or resource busy";
    case 17: return "File exists";
    case 18: return "Invalid cross-device link";
    case 19: return "No such device";
    case 20: return "Not a directory";
    case 21: return "Is a directory";
    case 22: return "Invalid argument";
    case 23: return "Too many open files in system";
    case 24: return "Too many open files";
    case 25: return "Inappropriate ioctl for device";
    case 27: return "File too large";
    case 28: return "No space left on device";
    case 29: return "Illegal seek";
    case 30: return "Read-only file system";
    case 31: return "Too many links";
    case 32: return "Broken pipe";
    case 33: return "Numerical argument out of domain";
    case 34: return "Numerical result out of range";
    case 35: return "Resource deadlock avoided";
    case 36: return "File name too long";
    case 37: return "No locks available";
    case 38: return "Function not implemented";
    case 39: return "Directory not empty";
    case 40: return "Too many levels of symbolic links";
    default: return "Unknown error";
    }
}

/* ====================================================================
 * 2. String concatenation / span
 * ==================================================================== */

char *strncat(char *dest, const char *src, size_t n) {
    char *d = dest + strlen(dest);
    size_t i;
    for (i = 0; i < n && src[i]; i++)
        d[i] = src[i];
    d[i] = '\0';
    return dest;
}

size_t strspn(const char *s, const char *accept) {
    size_t count = 0;
    for (; *s; s++) {
        const char *a = accept;
        int found = 0;
        while (*a) {
            if (*s == *a) { found = 1; break; }
            a++;
        }
        if (!found) break;
        count++;
    }
    return count;
}

size_t strcspn(const char *s, const char *reject) {
    size_t count = 0;
    for (; *s; s++) {
        const char *r = reject;
        while (*r) {
            if (*s == *r) return count;
            r++;
        }
        count++;
    }
    return count;
}

/* ====================================================================
 * 3. strtok / strtok_r
 * ==================================================================== */

char *strtok_r(char *str, const char *delim, char **saveptr) {
    if (str) *saveptr = str;
    if (!*saveptr) return NULL;

    /* Skip leading delimiters */
    char *start = *saveptr;
    start += strspn(start, delim);
    if (*start == '\0') {
        *saveptr = NULL;
        return NULL;
    }

    /* Find end of token */
    char *end = start + strcspn(start, delim);
    if (*end) {
        *end = '\0';
        *saveptr = end + 1;
    } else {
        *saveptr = NULL;
    }
    return start;
}

char *strtok(char *str, const char *delim) {
    static char *_strtok_state = NULL;
    return strtok_r(str, delim, &_strtok_state);
}

/* ====================================================================
 * 4. strndup / strnlen / memchr
 * ==================================================================== */

size_t strnlen(const char *s, size_t maxlen) {
    size_t len = 0;
    while (len < maxlen && s[len]) len++;
    return len;
}

char *strndup(const char *s, size_t n) {
    size_t len = strnlen(s, n);
    char *dup = (char *)malloc(len + 1);
    if (dup) {
        memcpy(dup, s, len);
        dup[len] = '\0';
    }
    return dup;
}

void *memchr(const void *s, int c, size_t n) {
    const unsigned char *p = (const unsigned char *)s;
    unsigned char uc = (unsigned char)c;
    while (n--) {
        if (*p == uc) return (void *)p;
        p++;
    }
    return NULL;
}

/* ====================================================================
 * 5. Case-insensitive comparison
 * ==================================================================== */

static int _tolower(int c) {
    return (c >= 'A' && c <= 'Z') ? c + 32 : c;
}

int strcasecmp(const char *s1, const char *s2) {
    while (*s1 && *s2) {
        int c1 = _tolower((unsigned char)*s1);
        int c2 = _tolower((unsigned char)*s2);
        if (c1 != c2) return c1 - c2;
        s1++;
        s2++;
    }
    return _tolower((unsigned char)*s1) - _tolower((unsigned char)*s2);
}

int strncasecmp(const char *s1, const char *s2, size_t n) {
    if (n == 0) return 0;
    while (n-- > 1 && *s1 && *s2) {
        int c1 = _tolower((unsigned char)*s1);
        int c2 = _tolower((unsigned char)*s2);
        if (c1 != c2) return c1 - c2;
        s1++;
        s2++;
    }
    return _tolower((unsigned char)*s1) - _tolower((unsigned char)*s2);
}
