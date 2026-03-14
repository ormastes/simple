/*
 * Minimal bare-metal runtime glue for Simple-built test images.
 *
 * Provides the symbols expected by the startup assembly without pulling in
 * the hosted runtime or constructor support.
 *
 * Includes semihosting I/O for QEMU targets so that print/println produce
 * visible output on the host terminal.
 */

#include <stdint.h>

extern long long __simple_main(void);
extern char __bss_start[];
extern char __bss_end[];

/* Forward declarations */
void __spl_exit(int status) __attribute__((noreturn));
void *rt_alloc(int64_t size);
void *rt_array_new(int64_t cap);

static void zero_bss(void) {
    for (char *p = __bss_start; p < __bss_end; p++) {
        *p = 0;
    }
}

/* ================================================================
 * Semihosting I/O
 * ================================================================ */

#if defined(__riscv)

/* RISC-V semihosting uses the standard sequence:
 *   slli zero, zero, 0x1f  (NOP marker)
 *   ebreak                 (trap)
 *   srai zero, zero, 7     (NOP marker)
 * a0 = operation, a1 = parameter block */
static inline long semihost_call(long op, long arg) {
    register long a0 __asm__("a0") = op;
    register long a1 __asm__("a1") = arg;
    __asm__ volatile (
        ".option push\n"
        ".option norvc\n"
        "slli zero, zero, 0x1f\n"
        "ebreak\n"
        "srai zero, zero, 7\n"
        ".option pop\n"
        : "+r"(a0)
        : "r"(a1)
        : "memory"
    );
    return a0;
}

#define SH_SYS_WRITE0  0x04   /* Write null-terminated string */
#define SH_SYS_WRITEC  0x03   /* Write single character */
#define SH_SYS_EXIT    0x18   /* Exit */

static void sh_write_string(const char *s) {
    semihost_call(SH_SYS_WRITE0, (long)s);
}

static void sh_write_char(char c) {
    semihost_call(SH_SYS_WRITEC, (long)&c);
}

#elif defined(__arm__) || defined(__aarch64__)

/* ARM semihosting via BKPT (Thumb) or HLT (AArch64) */
static inline long semihost_call(long op, long arg) {
    register long r0 __asm__("r0") = op;
    register long r1 __asm__("r1") = arg;
#if defined(__aarch64__)
    __asm__ volatile ("hlt #0xF000" : "+r"(r0) : "r"(r1) : "memory");
#else
    __asm__ volatile ("bkpt #0xAB" : "+r"(r0) : "r"(r1) : "memory");
#endif
    return r0;
}

#define SH_SYS_WRITE0  0x04
#define SH_SYS_WRITEC  0x03
#define SH_SYS_EXIT    0x18

static void sh_write_string(const char *s) {
    semihost_call(SH_SYS_WRITE0, (long)s);
}

static void sh_write_char(char c) {
    semihost_call(SH_SYS_WRITEC, (long)&c);
}

#else

/* Fallback: no semihosting — output is discarded */
static void sh_write_string(const char *s) { (void)s; }
static void sh_write_char(char c) { (void)c; }

#endif

/* ================================================================
 * Runtime I/O functions (called by compiler-generated LLVM IR)
 * ================================================================ */

void rt_print(const char *s) {
    if (s) sh_write_string(s);
}

void rt_println(const char *s) {
    if (s) sh_write_string(s);
    sh_write_char('\n');
}

void rt_print_value(const char *s) { rt_print(s); }
void rt_println_value(const char *s) { rt_println(s); }
void rt_eprint(const char *s) { rt_print(s); }
void rt_eprintln(const char *s) { rt_println(s); }
void rt_eprint_value(const char *s) { rt_print(s); }
void rt_eprintln_value(const char *s) { rt_println(s); }

/* ================================================================
 * Minimal memory allocator (bump allocator for baremetal)
 * ================================================================ */

extern char _heap_start[];
extern char _heap_end[];

static char *heap_ptr = 0;

static void heap_init(void) {
    if (!heap_ptr) heap_ptr = _heap_start;
}

void *rt_alloc(int64_t size) {
    heap_init();
    /* Align to 8 bytes */
    int64_t aligned = (size + 7) & ~7;
    if (heap_ptr + aligned > _heap_end) return (void*)0;
    void *p = heap_ptr;
    heap_ptr += aligned;
    return p;
}

void *rt_realloc(void *ptr, int64_t size) {
    /* Bump allocator: allocate new block, copy old data */
    void *new_ptr = rt_alloc(size);
    if (new_ptr && ptr) {
        char *dst = (char *)new_ptr;
        char *src = (char *)ptr;
        for (int64_t i = 0; i < size; i++) dst[i] = src[i];
    }
    return new_ptr;
}

void rt_free(void *ptr) {
    (void)ptr; /* Bump allocator: no-op */
}

void *rt_memcpy(void *dst, const void *src, int64_t n) {
    char *d = (char *)dst;
    const char *s = (const char *)src;
    for (int64_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

void *rt_memset(void *dst, int8_t val, int64_t n) {
    char *d = (char *)dst;
    for (int64_t i = 0; i < n; i++) d[i] = val;
    return dst;
}

int64_t rt_memcmp(const void *a, const void *b, int64_t n) {
    const unsigned char *pa = (const unsigned char *)a;
    const unsigned char *pb = (const unsigned char *)b;
    for (int64_t i = 0; i < n; i++) {
        if (pa[i] != pb[i]) return pa[i] < pb[i] ? -1 : 1;
    }
    return 0;
}

/* ================================================================
 * Minimal string operations
 * ================================================================ */

int64_t rt_strlen(const char *s) {
    if (!s) return 0;
    int64_t len = 0;
    while (s[len]) len++;
    return len;
}

int64_t rt_strcmp(const char *a, const char *b) {
    if (!a && !b) return 0;
    if (!a) return -1;
    if (!b) return 1;
    while (*a && *b && *a == *b) { a++; b++; }
    return (unsigned char)*a - (unsigned char)*b;
}

char *rt_strcat(const char *a, const char *b) {
    int64_t la = rt_strlen(a);
    int64_t lb = rt_strlen(b);
    char *result = (char *)rt_alloc(la + lb + 1);
    if (!result) return "";
    rt_memcpy(result, a, la);
    rt_memcpy(result + la, b, lb);
    result[la + lb] = 0;
    return result;
}

char *rt_substr(const char *s, int64_t start, int64_t len) {
    if (!s) return "";
    int64_t slen = rt_strlen(s);
    if (start >= slen) return "";
    if (start + len > slen) len = slen - start;
    char *result = (char *)rt_alloc(len + 1);
    if (!result) return "";
    rt_memcpy(result, s + start, len);
    result[len] = 0;
    return result;
}

int64_t rt_strfind(const char *haystack, const char *needle) {
    if (!haystack || !needle) return -1;
    int64_t hlen = rt_strlen(haystack);
    int64_t nlen = rt_strlen(needle);
    if (nlen > hlen) return -1;
    for (int64_t i = 0; i <= hlen - nlen; i++) {
        int found = 1;
        for (int64_t j = 0; j < nlen; j++) {
            if (haystack[i+j] != needle[j]) { found = 0; break; }
        }
        if (found) return i;
    }
    return -1;
}

char *rt_strreplace(const char *s, const char *old, const char *new_s) {
    (void)old; (void)new_s;
    /* Minimal stub — return copy of original */
    int64_t len = rt_strlen(s);
    char *result = (char *)rt_alloc(len + 1);
    if (!result) return "";
    rt_memcpy(result, s, len + 1);
    return result;
}

void *rt_strsplit(const char *s, const char *sep) {
    (void)s; (void)sep;
    return rt_array_new(0);
}

/* ================================================================
 * Minimal string object operations
 * ================================================================ */

char *rt_string_new(const char *s) {
    if (!s) return "";
    int64_t len = rt_strlen(s);
    char *copy = (char *)rt_alloc(len + 1);
    if (!copy) return "";
    rt_memcpy(copy, s, len + 1);
    return copy;
}

char *rt_string_concat(const char *a, const char *b) { return rt_strcat(a, b); }

int rt_string_starts_with(const char *s, const char *prefix) {
    if (!s || !prefix) return 0;
    int64_t plen = rt_strlen(prefix);
    return rt_memcmp(s, prefix, plen) == 0 ? 1 : 0;
}

int rt_string_ends_with(const char *s, const char *suffix) {
    if (!s || !suffix) return 0;
    int64_t slen = rt_strlen(s);
    int64_t suflen = rt_strlen(suffix);
    if (suflen > slen) return 0;
    return rt_memcmp(s + slen - suflen, suffix, suflen) == 0 ? 1 : 0;
}

char *rt_to_string(const char *s) { return rt_string_new(s); }
char *rt_string_join(const char *a, const char *b) { return rt_strcat(a, b); }
char *rt_string_split(const char *s, const char *sep) { return (char*)rt_strsplit(s, sep); }
char *rt_string_replace(const char *s, const char *old, const char *new_s) { return rt_strreplace(s, old, new_s); }
char *rt_string_trim(const char *s) { return rt_string_new(s); }
char *rt_string_char_at(const char *s, int64_t idx) {
    char buf[2] = { s[idx], 0 };
    return rt_string_new(buf);
}
int rt_string_contains(const char *s, const char *sub) { return rt_strfind(s, sub) >= 0 ? 1 : 0; }
char *rt_string_to_lower(const char *s) { return rt_string_new(s); }
char *rt_string_to_upper(const char *s) { return rt_string_new(s); }

/* ================================================================
 * Number/string conversion
 * ================================================================ */

int64_t rt_to_int(const char *s) {
    if (!s) return 0;
    int64_t result = 0;
    int neg = 0;
    if (*s == '-') { neg = 1; s++; }
    while (*s >= '0' && *s <= '9') {
        result = result * 10 + (*s - '0');
        s++;
    }
    return neg ? -result : result;
}

double rt_to_float(const char *s) {
    (void)s;
    return 0.0;
}

char *rt_int_to_string(int64_t n) {
    char buf[24];
    int i = 0;
    int neg = 0;
    if (n < 0) { neg = 1; n = -n; }
    if (n == 0) { buf[i++] = '0'; }
    else {
        while (n > 0) { buf[i++] = '0' + (n % 10); n /= 10; }
    }
    if (neg) buf[i++] = '-';
    /* Reverse */
    char *result = (char *)rt_alloc(i + 1);
    if (!result) return "0";
    for (int j = 0; j < i; j++) result[j] = buf[i - 1 - j];
    result[i] = 0;
    return result;
}

char *rt_float_to_string(double f) {
    (void)f;
    return rt_string_new("0.0");
}

/* ================================================================
 * Minimal array operations (flat pointer array)
 *
 * Layout: [int64_t len][int64_t cap][ptr elements...]
 * ================================================================ */

typedef struct {
    int64_t len;
    int64_t cap;
    void *elements[];
} BmArray;

void *rt_array_new(int64_t cap) {
    if (cap < 4) cap = 4;
    BmArray *arr = (BmArray *)rt_alloc((int64_t)sizeof(BmArray) + cap * (int64_t)sizeof(void*));
    if (!arr) return (void*)0;
    arr->len = 0;
    arr->cap = cap;
    return arr;
}

int64_t rt_array_len(void *arr) {
    if (!arr) return 0;
    return ((BmArray *)arr)->len;
}

void *rt_array_get(void *arr, int64_t idx) {
    if (!arr) return (void*)0;
    BmArray *a = (BmArray *)arr;
    if (idx < 0 || idx >= a->len) return (void*)0;
    return a->elements[idx];
}

void rt_array_set(void *arr, int64_t idx, void *val) {
    if (!arr) return;
    BmArray *a = (BmArray *)arr;
    if (idx < 0 || idx >= a->len) return;
    a->elements[idx] = val;
}

void *rt_array_push(void *arr, void *val) {
    if (!arr) arr = rt_array_new(4);
    BmArray *a = (BmArray *)arr;
    if (a->len >= a->cap) {
        int64_t new_cap = a->cap * 2;
        BmArray *new_arr = (BmArray *)rt_alloc((int64_t)sizeof(BmArray) + new_cap * (int64_t)sizeof(void*));
        if (!new_arr) return arr;
        new_arr->len = a->len;
        new_arr->cap = new_cap;
        for (int64_t i = 0; i < a->len; i++) new_arr->elements[i] = a->elements[i];
        a = new_arr;
    }
    a->elements[a->len++] = val;
    return a;
}

void *rt_array_pop(void *arr) {
    if (!arr) return (void*)0;
    BmArray *a = (BmArray *)arr;
    if (a->len == 0) return (void*)0;
    return a->elements[--a->len];
}

void *rt_array_slice(void *arr, int64_t start, int64_t end) {
    if (!arr) return rt_array_new(0);
    BmArray *a = (BmArray *)arr;
    if (start < 0) start = 0;
    if (end > a->len) end = a->len;
    int64_t n = end - start;
    if (n <= 0) return rt_array_new(0);
    void *result = rt_array_new(n);
    for (int64_t i = 0; i < n; i++) rt_array_push(result, a->elements[start + i]);
    return result;
}

int rt_array_contains(void *arr, void *val) {
    (void)arr; (void)val;
    return 0;
}

void *rt_array_concat(void *a, void *b) {
    void *result = rt_array_new(rt_array_len(a) + rt_array_len(b));
    for (int64_t i = 0; i < rt_array_len(a); i++) rt_array_push(result, rt_array_get(a, i));
    for (int64_t i = 0; i < rt_array_len(b); i++) rt_array_push(result, rt_array_get(b, i));
    return result;
}

void *rt_array_sort(void *arr) { return arr; }
void *rt_array_reverse(void *arr) { return arr; }
void *rt_array_map(void *arr, void *fn) { (void)fn; return arr; }
void *rt_array_filter(void *arr, void *fn) { (void)fn; return arr; }
void *rt_array_copy(void *arr) { return arr; }

/* ================================================================
 * Minimal dict operations (stub — returns empty structures)
 * ================================================================ */

void *rt_dict_new(void)                          { return rt_alloc(64); }
void *rt_dict_get(void *d, void *k)              { (void)d; (void)k; return (void*)0; }
void  rt_dict_set(void *d, void *k, void *v)     { (void)d; (void)k; (void)v; }
int   rt_dict_contains(void *d, void *k)         { (void)d; (void)k; return 0; }
int64_t rt_dict_len(void *d)                     { (void)d; return 0; }
void  rt_dict_insert(void *d, void *k, void *v)  { (void)d; (void)k; (void)v; }
int   rt_dict_remove(void *d, void *k)           { (void)d; (void)k; return 0; }
void *rt_dict_keys(void *d)                      { (void)d; return rt_array_new(0); }
void *rt_dict_values(void *d)                    { (void)d; return rt_array_new(0); }
void  rt_dict_clear(void *d)                     { (void)d; }

/* ================================================================
 * Value comparison / type ops
 * ================================================================ */

int   rt_value_eq(void *a, void *b)              { return a == b ? 1 : 0; }
int64_t rt_native_eq(int64_t a, int64_t b)       { return a == b ? 1 : 0; }
int64_t rt_native_neq(int64_t a, int64_t b)      { return a != b ? 1 : 0; }
int   rt_is_none(void *p)                        { return p == (void*)0 ? 1 : 0; }
int   rt_is_some(void *p)                        { return p != (void*)0 ? 1 : 0; }
char *rt_typeof(void *p)                         { (void)p; return "unknown"; }

void *rt_enum_payload(void *p)                   { return p; }
int   rt_enum_check_discriminant(void *p, int64_t d) { (void)d; return p != (void*)0; }

/* ================================================================
 * Process / environment / time stubs
 * ================================================================ */

void *rt_get_args(void) { return rt_array_new(0); }
int64_t rt_get_argc(void) { return 0; }
void rt_set_args(int64_t argc, void *argv) { (void)argc; (void)argv; }
int64_t rt_time_now_unix(void) { return 0; }
int64_t rt_time_now_unix_millis(void) { return 0; }
int64_t rt_time_now_unix_micros(void) { return 0; }
void rt_sleep_ms(int64_t ms) { (void)ms; }
char *rt_readline(void) { return ""; }
int64_t rt_native_build(const char *s) { (void)s; return 0; }
int64_t rt_getpid(void) { return 0; }
int rt_mkdir_p(const char *s) { (void)s; return 0; }
void *rt_getenv(const char *s) { (void)s; return (void*)0; }
int rt_setenv(const char *k, const char *v) { (void)k; (void)v; return 0; }
void rt_exit(int64_t code) { __spl_exit((int)code); }

/* File operations — all fail gracefully on baremetal */
void *rt_file_open(const char *p, const char *m) { (void)p; (void)m; return (void*)0; }
void  rt_file_close(void *f) { (void)f; }
char *rt_file_read_text(const char *p) { (void)p; return ""; }
int   rt_file_write(const char *p, const char *d) { (void)p; (void)d; return 0; }
void *rt_file_read_bytes(const char *p) { (void)p; return (void*)0; }
int   rt_file_write_bytes(const char *p, void *d, int64_t n) { (void)p; (void)d; (void)n; return 0; }
int   rt_file_exists(const char *p) { (void)p; return 0; }
int   rt_file_delete(const char *p) { (void)p; return 0; }
int   rt_file_copy(const char *a, const char *b) { (void)a; (void)b; return 0; }
int   rt_file_move(const char *a, const char *b) { (void)a; (void)b; return 0; }
int64_t rt_file_size(const char *p) { (void)p; return 0; }
int   rt_file_lock(const char *p) { (void)p; return 0; }
int   rt_file_unlock(const char *p) { (void)p; return 0; }
void *rt_dir_list(const char *p) { (void)p; return rt_array_new(0); }
int   rt_dir_create(const char *p) { (void)p; return 0; }
int   rt_dir_delete(const char *p) { (void)p; return 0; }
int   rt_dir_exists(const char *p) { (void)p; return 0; }
void *rt_process_spawn(const char *cmd, void *args, int64_t n) { (void)cmd; (void)args; (void)n; return (void*)0; }
int64_t rt_process_wait(void *h) { (void)h; return -1; }

/* Math — use builtins where possible */
double rt_sin(double x)           { return __builtin_sin(x); }
double rt_cos(double x)           { return __builtin_cos(x); }
double rt_sqrt(double x)          { return __builtin_sqrt(x); }
double rt_pow(double x, double y) { return __builtin_pow(x, y); }
double rt_abs(double x)           { return x < 0 ? -x : x; }
double rt_floor(double x)         { return __builtin_floor(x); }
double rt_ceil(double x)          { return __builtin_ceil(x); }
double rt_log(double x)           { return __builtin_log(x); }
double rt_exp(double x)           { return __builtin_exp(x); }
double rt_tan(double x)           { return __builtin_tan(x); }
double rt_atan2(double y, double x) { return __builtin_atan2(y, x); }

/* ================================================================
 * Panic — print message and halt
 * ================================================================ */

void rt_panic(const char *msg) {
    rt_println(msg);
    __spl_exit(1);
}

/* ================================================================
 * Original startup glue
 * ================================================================ */

void spl_thread_init(void) {}

void spl_init_args(int argc, char **argv) {
    (void)argc;
    (void)argv;
}

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    return (int)__simple_main();
}

void __spl_exit(int status) {
    (void)status;
#if defined(__riscv)
    /* Use semihosting SYS_EXIT for clean QEMU shutdown */
    {
#if __riscv_xlen == 64
        uint64_t args[2] = { 0x20026, (uint64_t)status }; /* ADP_Stopped_ApplicationExit */
        semihost_call(SH_SYS_EXIT, (long)args);
#else
        uint32_t args[2] = { 0x20026, (uint32_t)status };
        semihost_call(SH_SYS_EXIT, (long)args);
#endif
    }
    __asm__ volatile (
        "csrci mstatus, 0x8\n"
        "1: wfi\n"
        "j 1b\n"
    );
#elif defined(__x86_64__) || defined(__i386__)
    __asm__ volatile (
        "cli\n"
        "1: hlt\n"
        "jmp 1b\n"
    );
#elif defined(__aarch64__)
    __asm__ volatile (
        "msr daifset, #0xF\n"
        "1: wfi\n"
        "b 1b\n"
    );
#elif defined(__arm__)
    __asm__ volatile (
        "cpsid if\n"
        "1: wfi\n"
        "b 1b\n"
    );
#else
    for (;;) {}
#endif
    __builtin_unreachable();
}

void __spl_start_bare(void) {
    zero_bss();
    __spl_exit(main(0, (char **)0));
}
