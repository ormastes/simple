/* Direct C ABI reproduction: link the complete production translation unit.
 * No copied implementations, invented production types, or mocked helpers.
 * This is NOT a Simple compiler or boot/device acceptance test. */
#include <stdint.h>
#include <stddef.h>

typedef int64_t Value;
extern Value rt_and(Value, Value);
extern Value rt_or(Value, Value);
extern Value rt_not(Value);
extern Value rt_to_bool(Value);
extern Value rt_is_bool(Value);

static long write_stdout(const char *s, size_t n) {
#if defined(__x86_64__)
    register long ax __asm__("rax") = 1;
    register long di __asm__("rdi") = 1;
    register const char *si __asm__("rsi") = s;
    register size_t dx __asm__("rdx") = n;
    __asm__ volatile("syscall" : "+a"(ax) : "D"(di), "S"(si), "d"(dx) : "rcx", "r11", "memory");
    return ax;
#elif defined(__aarch64__)
    register long x0 __asm__("x0") = 1;
    register const char *x1 __asm__("x1") = s;
    register size_t x2 __asm__("x2") = n;
    register long x8 __asm__("x8") = 64;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x8) : "memory", "cc");
    return x0;
#else
#error unsupported architecture
#endif
}
static void text(const char *s) {
    size_t n = 0;
    while (s[n]) ++n;
    while (n) {
        long wrote = write_stdout(s, n);
        if (wrote <= 0) return;
        s += wrote;
        n -= (size_t)wrote;
    }
}
static void number(uint64_t v) {
    char b[21]; size_t n = sizeof b;
    do { b[--n] = (char)('0' + v % 10); v /= 10; } while (v);
    write_stdout(b + n, sizeof b - n);
}
static unsigned checked, failed;
static void expect(const char *name, unsigned i, unsigned j, Value got, Value want) {
    ++checked;
    if (got == want) return;
    ++failed;
    text("FAIL "); text(name); text(" i="); number(i); text(" j="); number(j);
    text(" got="); number((uint64_t)got); text(" want="); number((uint64_t)want); text("\n");
}
struct Case { Value value; int truth; int is_bool; };
/* ABI oracle independent of production macros: true=11, false=19, nil=3,
 * integers have tag zero and are shifted by three. Avoid negative C shifts. */
static const struct Case cases[] = {
    {11, 1, 1}, {19, 0, 1}, {0, 0, 0}, {8, 1, 0}, {16, 1, 0},
    {-8, 1, 0}, {3, 0, 0}, {INT64_MIN, 1, 0}, {INT64_MAX - 7, 1, 0}
};
int repro_main(void) {
    const unsigned n = sizeof cases / sizeof cases[0];
    /* First check reproduces the original tagged-false negation defect. */
    expect("original_not_false", 1, 0, rt_not(19), 11);
    for (unsigned i = 0; i < n; ++i) {
        expect("not", i, 0, rt_not(cases[i].value), cases[i].truth ? 19 : 11);
        expect("to_bool", i, 0, rt_to_bool(cases[i].value), cases[i].truth ? 11 : 19);
        /* rt_is_bool's historical return ABI is raw 0/1, not tagged. */
        expect("is_bool", i, 0, rt_is_bool(cases[i].value), cases[i].is_bool);
        for (unsigned j = 0; j < n; ++j) {
            expect("and", i, j, rt_and(cases[i].value, cases[j].value),
                   cases[i].truth && cases[j].truth ? 11 : 19);
            expect("or", i, j, rt_or(cases[i].value, cases[j].value),
                   cases[i].truth || cases[j].truth ? 11 : 19);
        }
    }
    text("checked="); number(checked); text(" failed="); number(failed); text("\n");
    return failed ? 1 : 0;
}
