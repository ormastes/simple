/*
 * SimpleOS Libc Shim — Implementation
 *
 * Minimal C runtime mapping standard libc calls to SimpleOS syscalls.
 * Sufficient for bootstrapping LLVM/Clang and Rust on SimpleOS.
 *
 * Syscall numbers (from src/os/kernel/ipc/syscall.spl):
 *   0  = Exit          4  = GetPid
 *  10  = Mmap         11  = Munmap        12  = Mprotect
 *  30  = Open         31  = Read          32  = Write         33  = Close
 *  34  = Stat
 *  60  = DebugWrite (serial output)
 *
 * Syscall ABI (x86_64, from src/os/userlib/syscall_raw.spl):
 *   rax = id, rdi = arg0, rsi = arg1, rdx = arg2, r10 = arg3, r8 = arg4
 *   result in rax
 */

#include "simpleos_libc.h"

/* ====================================================================
 * 1. Syscall interface
 * ==================================================================== */

/*
 * Syscall trampoline — implemented in simpleos_syscall.S (x86_64 assembly).
 * Uses: rax=id, rdi=a0, rsi=a1, rdx=a2, r10=a3, r8=a4; result in rax.
 */
extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                 int64_t a2, int64_t a3, int64_t a4);

/* ====================================================================
 * 2. Errno
 * ==================================================================== */

int errno = 0;

/* Helper: set errno from negative syscall result, return -1 */
static int set_errno(int64_t r) {
    errno = (int)(-r);
    return -1;
}

/* ====================================================================
 * 3. Memory allocation — bump allocator using mmap
 * ==================================================================== */

#define PAGE_SIZE 4096
#define INITIAL_HEAP (64 * 1024 * 1024)  /* 64 MB */

static uint8_t *heap_base = NULL;
static size_t   heap_used = 0;
static size_t   heap_size = 0;

__attribute__((weak))
void *malloc(size_t size) {
    if (size == 0) return NULL;

    /* Lazy init: allocate initial heap via Mmap syscall (10) */
    if (!heap_base) {
        int64_t r = simpleos_syscall(10, 0, INITIAL_HEAP, 3 /* RW */, 0, 0);
        if (r < 0) {
            errno = ENOMEM;
            return NULL;
        }
        heap_base = (uint8_t *)r;
        heap_size = INITIAL_HEAP;
    }

    /* 16-byte alignment */
    size = (size + 15) & ~(size_t)15;

    if (heap_used + size > heap_size) {
        /* Expand: request more pages */
        size_t expand = (size > INITIAL_HEAP) ? size * 2 : INITIAL_HEAP;
        int64_t r = simpleos_syscall(10, 0, (int64_t)expand, 3 /* RW */, 0, 0);
        if (r < 0) {
            errno = ENOMEM;
            return NULL;
        }
        /*
         * If the new region is contiguous with the existing heap, extend.
         * Otherwise, move to the new region (losing the unused tail).
         */
        if ((uint8_t *)r == heap_base + heap_size) {
            heap_size += expand;
        } else {
            heap_base = (uint8_t *)r;
            heap_size = expand;
            heap_used = 0;
        }
    }

    void *ptr = heap_base + heap_used;
    heap_used += size;
    return ptr;
}

__attribute__((weak))
void free(void *ptr) {
    /* Bump allocator — no individual free (sufficient for compiler bootstrapping) */
    (void)ptr;
}

__attribute__((weak))
void *calloc(size_t nmemb, size_t size) {
    size_t total = nmemb * size;
    void *p = malloc(total);
    if (p) memset(p, 0, total);
    return p;
}

__attribute__((weak))
void *realloc(void *ptr, size_t size) {
    if (!ptr) return malloc(size);
    if (size == 0) { free(ptr); return NULL; }

    void *new_ptr = malloc(size);
    if (new_ptr && ptr) {
        /* Copy conservatively — may over-read for bump allocator, but safe
         * within the heap region. For a proper allocator, we'd store sizes. */
        memcpy(new_ptr, ptr, size);
    }
    return new_ptr;
}

/* ====================================================================
 * 4. mmap / munmap
 * ==================================================================== */

void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset) {
    (void)flags; (void)fd; (void)offset;
    int64_t r = simpleos_syscall(10, (int64_t)(uintptr_t)addr, (int64_t)length,
                                  (int64_t)prot, 0, 0);
    if (r < 0) {
        errno = ENOMEM;
        return MAP_FAILED;
    }
    return (void *)(uintptr_t)r;
}

int munmap(void *addr, size_t length) {
    int64_t r = simpleos_syscall(11, (int64_t)(uintptr_t)addr, (int64_t)length,
                                  0, 0, 0);
    if (r < 0) return set_errno(r);
    return 0;
}

/* ====================================================================
 * 5. String operations
 * ==================================================================== */

size_t strlen(const char *s) {
    const char *p = s;
    while (*p) p++;
    return (size_t)(p - s);
}

char *strcpy(char *dest, const char *src) {
    char *d = dest;
    while ((*d++ = *src++)) {}
    return dest;
}

char *strncpy(char *dest, const char *src, size_t n) {
    size_t i;
    for (i = 0; i < n && src[i]; i++)
        dest[i] = src[i];
    for (; i < n; i++)
        dest[i] = '\0';
    return dest;
}

int strcmp(const char *s1, const char *s2) {
    while (*s1 && *s1 == *s2) { s1++; s2++; }
    return (unsigned char)*s1 - (unsigned char)*s2;
}

int strncmp(const char *s1, const char *s2, size_t n) {
    if (n == 0) return 0;
    while (n-- > 1 && *s1 && *s1 == *s2) { s1++; s2++; }
    return (unsigned char)*s1 - (unsigned char)*s2;
}

char *strcat(char *dest, const char *src) {
    char *d = dest + strlen(dest);
    while ((*d++ = *src++)) {}
    return dest;
}

char *strchr(const char *s, int c) {
    while (*s) {
        if (*s == (char)c) return (char *)s;
        s++;
    }
    return (c == '\0') ? (char *)s : NULL;
}

char *strrchr(const char *s, int c) {
    const char *last = NULL;
    while (*s) {
        if (*s == (char)c) last = s;
        s++;
    }
    if (c == '\0') return (char *)s;
    return (char *)last;
}

char *strstr(const char *haystack, const char *needle) {
    if (!*needle) return (char *)haystack;
    size_t nlen = strlen(needle);
    while (*haystack) {
        if (*haystack == *needle && strncmp(haystack, needle, nlen) == 0)
            return (char *)haystack;
        haystack++;
    }
    return NULL;
}

char *strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *dup = (char *)malloc(len);
    if (dup) memcpy(dup, s, len);
    return dup;
}

/* ====================================================================
 * 6. Memory operations
 * ==================================================================== */

void *memcpy(void *dest, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dest;
    const uint8_t *s = (const uint8_t *)src;
    while (n--) *d++ = *s++;
    return dest;
}

void *memmove(void *dest, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dest;
    const uint8_t *s = (const uint8_t *)src;
    if (d < s) {
        while (n--) *d++ = *s++;
    } else {
        d += n;
        s += n;
        while (n--) *--d = *--s;
    }
    return dest;
}

void *memset(void *dest, int c, size_t n) {
    uint8_t *d = (uint8_t *)dest;
    while (n--) *d++ = (uint8_t)c;
    return dest;
}

int memcmp(const void *s1, const void *s2, size_t n) {
    const uint8_t *a = (const uint8_t *)s1;
    const uint8_t *b = (const uint8_t *)s2;
    while (n--) {
        if (*a != *b) return *a - *b;
        a++; b++;
    }
    return 0;
}

/* ====================================================================
 * 7. I/O — FILE wrappers + POSIX file syscalls
 * ==================================================================== */

struct simpleos_FILE { int fd; };

static struct simpleos_FILE _stdin_f  = { 0 };
static struct simpleos_FILE _stdout_f = { 1 };
static struct simpleos_FILE _stderr_f = { 2 };

FILE *stdin  = &_stdin_f;
FILE *stdout = &_stdout_f;
FILE *stderr = &_stderr_f;

ssize_t write(int fd, const void *buf, size_t count) {
    if (fd == 1 || fd == 2) {
        /* Route stdout/stderr through DebugWrite (syscall 60) for serial */
        const char *p = (const char *)buf;
        for (size_t i = 0; i < count; i++) {
            simpleos_syscall(60, (int64_t)(unsigned char)p[i], 0, 0, 0, 0);
        }
        return (ssize_t)count;
    }
    int64_t r = simpleos_syscall(32, fd, (int64_t)(uintptr_t)buf, (int64_t)count, 0, 0);
    if (r < 0) { set_errno(r); return -1; }
    return (ssize_t)r;
}

ssize_t read(int fd, void *buf, size_t count) {
    int64_t r = simpleos_syscall(31, fd, (int64_t)(uintptr_t)buf, (int64_t)count, 0, 0);
    if (r < 0) { set_errno(r); return -1; }
    return (ssize_t)r;
}

int open(const char *path, int flags, ...) {
    size_t pathlen = strlen(path);
    int64_t r = simpleos_syscall(30, (int64_t)(uintptr_t)path, (int64_t)pathlen,
                                  (int64_t)flags, 0, 0);
    if (r < 0) return set_errno(r);
    return (int)r;
}

int close(int fd) {
    int64_t r = simpleos_syscall(33, fd, 0, 0, 0, 0);
    if (r < 0) return set_errno(r);
    return 0;
}

/* ====================================================================
 * 8. printf — minimal implementation
 *
 * Supported: %s %d %i %u %x %X %p %c %ld %li %lu %lx %lX %zu %zd %%
 *            Width and zero-padding (e.g. %08x), '-' left-align
 * ==================================================================== */

/* Write a single character into the snprintf buffer */
typedef struct {
    char  *buf;
    size_t pos;
    size_t max;
} fmt_state;

static void fmt_putc(fmt_state *st, char c) {
    if (st->pos < st->max) st->buf[st->pos] = c;
    st->pos++;
}

static void fmt_puts(fmt_state *st, const char *s) {
    while (*s) fmt_putc(st, *s++);
}

/* Unsigned decimal */
static void fmt_u64(fmt_state *st, uint64_t v, int width, int zero_pad) {
    char tmp[21];
    int  len = 0;
    if (v == 0) { tmp[len++] = '0'; }
    else { while (v) { tmp[len++] = '0' + (char)(v % 10); v /= 10; } }
    char pad = zero_pad ? '0' : ' ';
    for (int i = len; i < width; i++) fmt_putc(st, pad);
    for (int i = len - 1; i >= 0; i--) fmt_putc(st, tmp[i]);
}

/* Signed decimal */
static void fmt_i64(fmt_state *st, int64_t v, int width, int zero_pad) {
    if (v < 0) {
        fmt_putc(st, '-');
        if (width > 0) width--;
        /* Handle INT64_MIN */
        if (v == (-9223372036854775807LL - 1)) {
            fmt_puts(st, "9223372036854775808");
            return;
        }
        fmt_u64(st, (uint64_t)(-v), width, zero_pad);
    } else {
        fmt_u64(st, (uint64_t)v, width, zero_pad);
    }
}

/* Hexadecimal */
static void fmt_hex(fmt_state *st, uint64_t v, int upper, int width, int zero_pad) {
    const char *digits = upper ? "0123456789ABCDEF" : "0123456789abcdef";
    char tmp[17];
    int  len = 0;
    if (v == 0) { tmp[len++] = '0'; }
    else { while (v) { tmp[len++] = digits[v & 0xF]; v >>= 4; } }
    char pad = zero_pad ? '0' : ' ';
    for (int i = len; i < width; i++) fmt_putc(st, pad);
    for (int i = len - 1; i >= 0; i--) fmt_putc(st, tmp[i]);
}

/* Float formatting helper — implemented in simpleos_printf_float.c */
extern int _fmt_float(char *buf, size_t max, double val, char spec,
                       int width, int prec);

int vsnprintf(char *str, size_t size, const char *fmt, va_list ap) {
    fmt_state st;
    st.buf = str;
    st.pos = 0;
    st.max = (size > 0) ? size - 1 : 0;

    while (*fmt) {
        if (*fmt != '%') {
            fmt_putc(&st, *fmt++);
            continue;
        }
        fmt++; /* skip '%' */

        /* Flags */
        int left_align = 0;
        int zero_pad = 0;
        while (*fmt == '-' || *fmt == '0' || *fmt == '+' || *fmt == ' ') {
            if (*fmt == '-') left_align = 1;
            if (*fmt == '0') zero_pad = 1;
            fmt++;
        }
        if (left_align) zero_pad = 0;

        /* Width */
        int width = 0;
        if (*fmt == '*') {
            width = va_arg(ap, int);
            fmt++;
        } else {
            while (*fmt >= '0' && *fmt <= '9') {
                width = width * 10 + (*fmt - '0');
                fmt++;
            }
        }

        /* Precision */
        int prec = -1; /* -1 = not specified */
        if (*fmt == '.') {
            fmt++;
            prec = 0;
            if (*fmt == '*') {
                prec = va_arg(ap, int);
                fmt++;
            } else {
                while (*fmt >= '0' && *fmt <= '9') {
                    prec = prec * 10 + (*fmt - '0');
                    fmt++;
                }
            }
        }

        /* Length modifier */
        int is_long = 0;
        int is_size = 0;
        if (*fmt == 'l') { is_long = 1; fmt++; if (*fmt == 'l') fmt++; /* ll = l */ }
        else if (*fmt == 'z') { is_size = 1; fmt++; }

        /* Conversion */
        switch (*fmt) {
        case 'd': case 'i': {
            int64_t v = is_long || is_size ? va_arg(ap, int64_t) : (int64_t)va_arg(ap, int);
            fmt_i64(&st, v, width, zero_pad);
            break;
        }
        case 'u': {
            uint64_t v = is_long || is_size ? va_arg(ap, uint64_t) : (uint64_t)va_arg(ap, unsigned);
            fmt_u64(&st, v, width, zero_pad);
            break;
        }
        case 'x': case 'X': {
            uint64_t v = is_long || is_size ? va_arg(ap, uint64_t) : (uint64_t)va_arg(ap, unsigned);
            fmt_hex(&st, v, (*fmt == 'X'), width, zero_pad);
            break;
        }
        case 'p': {
            void *p = va_arg(ap, void *);
            fmt_puts(&st, "0x");
            fmt_hex(&st, (uint64_t)(uintptr_t)p, 0, 0, 0);
            break;
        }
        case 's': {
            const char *s = va_arg(ap, const char *);
            if (!s) s = "(null)";
            int slen = (int)strlen(s);
            /* Precision limits string length for %s */
            if (prec >= 0 && slen > prec) slen = prec;
            if (!left_align) {
                for (int i = slen; i < width; i++) fmt_putc(&st, ' ');
            }
            for (int i = 0; i < slen; i++) fmt_putc(&st, s[i]);
            if (left_align) {
                for (int i = slen; i < width; i++) fmt_putc(&st, ' ');
            }
            break;
        }
        case 'c': {
            char c = (char)va_arg(ap, int);
            fmt_putc(&st, c);
            break;
        }
        case 'f': case 'e': case 'E': case 'g': case 'G': {
            double v = va_arg(ap, double);
            char fbuf[80];
            int flen = _fmt_float(fbuf, sizeof(fbuf), v, *fmt, 0, prec);
            if (flen > (int)sizeof(fbuf) - 1) flen = (int)sizeof(fbuf) - 1;
            /* Width padding */
            if (!left_align) {
                for (int i = flen; i < width; i++)
                    fmt_putc(&st, zero_pad ? '0' : ' ');
            }
            for (int i = 0; i < flen; i++) fmt_putc(&st, fbuf[i]);
            if (left_align) {
                for (int i = flen; i < width; i++) fmt_putc(&st, ' ');
            }
            break;
        }
        case '%':
            fmt_putc(&st, '%');
            break;
        default:
            fmt_putc(&st, '%');
            fmt_putc(&st, *fmt);
            break;
        }
        if (*fmt) fmt++;
    }

    /* Null-terminate */
    if (size > 0) {
        if (st.pos < size)
            str[st.pos] = '\0';
        else
            str[size - 1] = '\0';
    }
    return (int)st.pos;
}

int snprintf(char *str, size_t size, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(str, size, fmt, ap);
    va_end(ap);
    return n;
}

int printf(const char *fmt, ...) {
    char buf[1024];
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    if (n > 0) write(1, buf, (size_t)(n > 1024 ? 1024 : n));
    return n;
}

int fprintf(FILE *stream, const char *fmt, ...) {
    char buf[1024];
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    if (n > 0) write(stream->fd, buf, (size_t)(n > 1024 ? 1024 : n));
    return n;
}

int puts(const char *s) {
    size_t len = strlen(s);
    write(1, s, len);
    write(1, "\n", 1);
    return (int)len + 1;
}

int fputs(const char *s, FILE *stream) {
    size_t len = strlen(s);
    write(stream->fd, s, len);
    return (int)len;
}

int fputc(int c, FILE *stream) {
    char ch = (char)c;
    write(stream->fd, &ch, 1);
    return (unsigned char)ch;
}

/* ====================================================================
 * 9. Process
 * ==================================================================== */

void exit(int status) {
    simpleos_syscall(0, (int64_t)status, 0, 0, 0, 0);
    __builtin_unreachable();
}

void abort(void) {
    exit(134);  /* SIGABRT convention */
}

int getpid(void) {
    return (int)simpleos_syscall(4, 0, 0, 0, 0, 0);
}

/* ====================================================================
 * 10. Time — full implementation in simpleos_time.c
 *     Environment — full implementation in simpleos_process.c
 * ==================================================================== */
