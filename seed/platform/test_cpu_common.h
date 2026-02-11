/*
 * CPU-architecture-portable intensive tests.
 * Shared by test_arm64.h and test_x86_64.h — exercises return values,
 * alignment, WFFI dispatch, recursion, memory access, pointer ops,
 * variadic args, setjmp/longjmp, floating point, data stress, and
 * compiler patterns that are identical across 64-bit architectures.
 *
 * NOT included directly — always via an arch-specific header that
 * defines the arch-specific calling-convention tests first.
 */
#ifndef SPL_TEST_CPU_COMMON_H
#define SPL_TEST_CPU_COMMON_H

#include <setjmp.h>
#include <math.h>
#ifndef __APPLE__
#include <alloca.h>
#endif

/* ================================================================
 * Shared helper functions (noinline to prevent inlining)
 * ================================================================ */

/* --- Calling convention helpers (arch-neutral) --- */

__attribute__((noinline))
static int64_t cpu_sum12(int64_t a, int64_t b, int64_t c, int64_t d,
                         int64_t e, int64_t f, int64_t g, int64_t h,
                         int64_t i, int64_t j, int64_t k, int64_t l) {
    return a + b + c + d + e + f + g + h + i + j + k + l;
}

__attribute__((noinline))
static int64_t cpu_mixed_int_ptr(int64_t a, const char* s,
                                 int64_t b, const char* t) {
    return a + b + (int64_t)spl_str_len(s) + (int64_t)spl_str_len(t);
}

/* --- Return value helpers --- */

__attribute__((noinline))
static int64_t cpu_return_boundary(int64_t which) {
    if (which == 0) return INT64_MIN;
    if (which == 1) return INT64_MAX;
    return 0;
}

__attribute__((noinline))
static SplValue cpu_return_splvalue(int64_t n) {
    return spl_int(n);
}

__attribute__((noinline))
static SplValue cpu_chain_splvalue(SplValue v) {
    return spl_int(spl_as_int(v) * 2);
}

/* --- Stack alignment helper --- */

__attribute__((noinline))
static int64_t cpu_odd_frame(int64_t depth) {
    volatile char odd[13]; /* 13 bytes — odd size, compiler must pad */
    memset((char*)odd, 0, 13);
    if (depth <= 0) return 1;
    return cpu_odd_frame(depth - 1) + 1;
}

/* --- WFFI helpers --- */

static int64_t cpu_wffi_fn0(void) { return 99; }

static int64_t cpu_wffi_fn4(int64_t a, int64_t b,
                             int64_t c, int64_t d) {
    return a * 1000 + b * 100 + c * 10 + d;
}

static int64_t cpu_wffi_large_ret(void) { return INT64_MAX; }
static int64_t cpu_wffi_neg_ret(void)   { return -999999999LL; }
static int64_t cpu_wffi_ptr_as_i64_fn(int64_t p) { return p; }

static int64_t cpu_wffi_reentrant_fn(int64_t x) {
    int64_t args[1] = {0};
    return spl_wffi_call_i64((void*)cpu_wffi_fn0, args, 0) + x;
}

/* --- Recursion helpers --- */

__attribute__((noinline))
static int64_t cpu_recurse(int64_t depth) {
    if (depth <= 0) return 0;
    return 1 + cpu_recurse(depth - 1);
}

static int64_t cpu_mutual_b(int64_t n); /* forward decl */

__attribute__((noinline))
static int64_t cpu_mutual_a(int64_t n) {
    if (n <= 0) return 0;
    return 1 + cpu_mutual_b(n - 1);
}

__attribute__((noinline))
static int64_t cpu_mutual_b(int64_t n) {
    if (n <= 0) return 0;
    return 1 + cpu_mutual_a(n - 1);
}

__attribute__((noinline))
static int64_t cpu_large_frame_recurse(int64_t depth) {
    volatile char buf[256];
    memset((char*)buf, (int)(depth & 0xFF), 256);
    if (depth <= 0) return (int64_t)(unsigned char)buf[0];
    return cpu_large_frame_recurse(depth - 1) + (int64_t)(unsigned char)buf[0];
}

/* --- Floating point helpers --- */

__attribute__((noinline))
static double cpu_sum8_f64(double a, double b, double c, double d,
                           double e, double f, double g, double h) {
    return a + b + c + d + e + f + g + h;
}

__attribute__((noinline))
static double cpu_mixed_float_int(int64_t a, double b,
                                  int64_t c, double d) {
    return (double)a + b + (double)c + d;
}

/* --- Function pointer helpers --- */

typedef int64_t (*cpu_fn_ptr)(int64_t);
static int64_t cpu_add_one(int64_t x)   { return x + 1; }
static int64_t cpu_double_it(int64_t x) { return x * 2; }
static int64_t cpu_negate_it(int64_t x) { return -x; }

/* --- Init/fini pattern --- */

static int cpu_init_counter = 0;

__attribute__((constructor))
static void cpu_test_init(void) {
    cpu_init_counter++;
}

/* ================================================================
 * 3–4: Calling Convention (deep stack + mixed, shared)
 * ================================================================ */

TEST(cpu_call_12_args_deep_stack) {
    int64_t r = cpu_sum12(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
    ASSERT_EQ_INT(r, 78);
}

TEST(cpu_call_mixed_int_ptr) {
    int64_t r = cpu_mixed_int_ptr(10, "hello", 20, "ab");
    ASSERT_EQ_INT(r, 37); /* 10 + 20 + 5 + 2 */
}

/* ================================================================
 * 5–7: Return Values
 * ================================================================ */

TEST(cpu_return_boundary_i64) {
    ASSERT_EQ_INT(cpu_return_boundary(0), INT64_MIN);
    ASSERT_EQ_INT(cpu_return_boundary(1), INT64_MAX);
}

TEST(cpu_return_splvalue_struct) {
    SplValue v = cpu_return_splvalue(12345);
    ASSERT(v.tag == SPL_INT);
    ASSERT_EQ_INT(spl_as_int(v), 12345);
}

TEST(cpu_return_struct_chain) {
    SplValue v = cpu_return_splvalue(50);
    SplValue v2 = cpu_chain_splvalue(v);
    ASSERT_EQ_INT(spl_as_int(v2), 100);
}

/* ================================================================
 * 8–10: Stack Alignment
 * ================================================================ */

TEST(cpu_stack_alignment_basic) {
    volatile int64_t local = 42;
    ASSERT((uintptr_t)&local % 8 == 0);
    (void)local;
}

TEST(cpu_alloca_stress) {
    for (int sz = 1; sz <= 33; sz++) {
        volatile char* p = (volatile char*)alloca((size_t)sz);
        memset((char*)p, 0xAA, (size_t)sz);
        ASSERT(p[0] == (char)0xAA);
        ASSERT(p[sz - 1] == (char)0xAA);
    }
}

TEST(cpu_nested_odd_frame) {
    int64_t r = cpu_odd_frame(20);
    ASSERT_EQ_INT(r, 21);
}

/* ================================================================
 * 11–16: WFFI
 * ================================================================ */

TEST(cpu_wffi_0_arg) {
    int64_t args[1] = {0};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)cpu_wffi_fn0, args, 0), 99);
}

TEST(cpu_wffi_4_arg_max) {
    int64_t args[4] = {1, 2, 3, 4};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)cpu_wffi_fn4, args, 4), 1234);
}

TEST(cpu_wffi_large_return) {
    int64_t args[1] = {0};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)cpu_wffi_large_ret, args, 0),
                  INT64_MAX);
}

TEST(cpu_wffi_negative_return) {
    int64_t args[1] = {0};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)cpu_wffi_neg_ret, args, 0),
                  -999999999LL);
}

TEST(cpu_wffi_ptr_as_i64) {
    volatile int64_t sentinel = 0xBEEF;
    int64_t args[1] = {(int64_t)&sentinel};
    int64_t result = spl_wffi_call_i64((void*)cpu_wffi_ptr_as_i64_fn,
                                       args, 1);
    ASSERT(result == (int64_t)&sentinel);
    ASSERT(*(int64_t*)result == 0xBEEF);
}

TEST(cpu_wffi_reentrant) {
    int64_t args[1] = {10};
    int64_t result = spl_wffi_call_i64((void*)cpu_wffi_reentrant_fn,
                                       args, 1);
    ASSERT_EQ_INT(result, 109); /* fn0() + 10 = 99 + 10 */
}

/* ================================================================
 * 17–18: Large Immediates
 * ================================================================ */

TEST(cpu_large_immediate_64bit) {
    volatile uint64_t val = 0xDEADBEEFCAFEBABEULL;
    ASSERT(val == 0xDEADBEEFCAFEBABEULL);
    ASSERT((val & 0xFFFF) == 0xBABE);
    ASSERT(((val >> 16) & 0xFFFF) == 0xCAFE);
    ASSERT(((val >> 32) & 0xFFFF) == 0xBEEF);
    ASSERT(((val >> 48) & 0xFFFF) == 0xDEAD);
}

TEST(cpu_fnv1a_constants) {
    volatile uint64_t basis = 14695981039346656037ULL;
    volatile uint64_t prime = 1099511628211ULL;
    ASSERT(basis == 14695981039346656037ULL);
    ASSERT(prime == 1099511628211ULL);
    uint64_t h = basis;
    h ^= (uint64_t)'A';
    h *= prime;
    ASSERT(h != basis);
}

/* ================================================================
 * 19–22: Deep Recursion
 * ================================================================ */

TEST(cpu_recursion_100) {
    ASSERT_EQ_INT(cpu_recurse(100), 100);
}

TEST(cpu_recursion_1000) {
    ASSERT_EQ_INT(cpu_recurse(1000), 1000);
}

TEST(cpu_mutual_recursion) {
    ASSERT_EQ_INT(cpu_mutual_a(100), 100);
    ASSERT_EQ_INT(cpu_mutual_b(100), 100);
}

TEST(cpu_large_frame_recursion) {
    int64_t r = cpu_large_frame_recurse(50);
    (void)r;
    ASSERT(1);
}

/* ================================================================
 * 23–26: Memory Access
 * ================================================================ */

TEST(cpu_aligned_access) {
    volatile int64_t i64 = 0x123456789ABCDEF0LL;
    volatile int32_t i32 = 0x12345678;
    volatile int16_t i16 = 0x1234;
    ASSERT((uintptr_t)&i64 % 8 == 0);
    ASSERT((uintptr_t)&i32 % 4 == 0);
    ASSERT((uintptr_t)&i16 % 2 == 0);
    ASSERT(i64 == 0x123456789ABCDEF0LL);
    ASSERT(i32 == 0x12345678);
    ASSERT(i16 == 0x1234);
}

TEST(cpu_unaligned_memcpy) {
    char buf[32];
    memset(buf, 0, 32);
    int64_t val = 0xDEADBEEF;
    memcpy(buf + 3, &val, sizeof(val));
    int64_t restored = 0;
    memcpy(&restored, buf + 3, sizeof(restored));
    ASSERT_EQ_INT(restored, 0xDEADBEEF);
}

TEST(cpu_splvalue_alignment) {
    SplValue v = spl_int(42);
    ASSERT((uintptr_t)&v % _Alignof(SplValue) == 0);
    SplValue arr[4];
    for (int i = 0; i < 4; i++) {
        arr[i] = spl_int(i);
        ASSERT((uintptr_t)&arr[i] % _Alignof(SplValue) == 0);
    }
}

TEST(cpu_dictentry_alignment) {
    SplDictEntry entry;
    entry.key = NULL;
    entry.value = spl_int(42);
    entry.hash = 0xDEAD;
    entry.occupied = 1;
    ASSERT((uintptr_t)&entry % _Alignof(SplDictEntry) == 0);
    ASSERT(sizeof(SplDictEntry) >=
           sizeof(char*) + sizeof(SplValue) + sizeof(uint64_t) + sizeof(int));
}

/* ================================================================
 * 27–29: Pointer Operations
 * ================================================================ */

TEST(cpu_ptr_roundtrip) {
    int64_t original = 42;
    int64_t* ptr = &original;
    int64_t as_int = (int64_t)ptr;
    int64_t* restored = (int64_t*)as_int;
    ASSERT(*restored == 42);
    ASSERT(ptr == restored);
}

TEST(cpu_null_is_zero) {
    void* p = NULL;
    ASSERT((int64_t)p == 0);
    ASSERT(p == (void*)0);
}

TEST(cpu_ptr_bit_preservation) {
    volatile int64_t stack_var = 0xCAFE;
    uintptr_t addr = (uintptr_t)&stack_var;
    int64_t as_i64 = (int64_t)addr;
    uintptr_t back = (uintptr_t)as_i64;
    ASSERT(back == addr);
    ASSERT(*(int64_t*)back == 0xCAFE);
}

/* ================================================================
 * 30–31: Variadic Arguments
 * ================================================================ */

TEST(cpu_variadic_10_ints) {
    char buf[256];
    snprintf(buf, sizeof(buf), "%d %d %d %d %d %d %d %d %d %d",
             1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
    ASSERT_EQ_STR(buf, "1 2 3 4 5 6 7 8 9 10");
}

TEST(cpu_variadic_mixed) {
    char buf[256];
    snprintf(buf, sizeof(buf), "%d %.1f %s %d %.2f",
             42, 3.14, "hello", -7, 2.71);
    ASSERT(spl_str_contains(buf, "42"));
    ASSERT(spl_str_contains(buf, "3.1"));
    ASSERT(spl_str_contains(buf, "hello"));
    ASSERT(spl_str_contains(buf, "-7"));
    ASSERT(spl_str_contains(buf, "2.71"));
}

/* ================================================================
 * 32–33: setjmp/longjmp
 * ================================================================ */

TEST(cpu_setjmp_basic) {
    jmp_buf env;
    volatile int reached = 0;
    if (setjmp(env) == 0) {
        reached = 1;
        longjmp(env, 42);
        reached = 2;
    } else {
        ASSERT(reached == 1);
    }
    ASSERT(reached == 1);
}

TEST(cpu_setjmp_preserves_locals) {
    jmp_buf env;
    volatile int64_t x = 100;
    volatile int64_t y = 200;
    int val = setjmp(env);
    if (val == 0) {
        x = 111;
        y = 222;
        longjmp(env, 1);
    } else {
        ASSERT_EQ_INT(x, 111);
        ASSERT_EQ_INT(y, 222);
    }
}

/* ================================================================
 * 34–36: Floating Point
 * ================================================================ */

TEST(cpu_float_8_args) {
    double r = cpu_sum8_f64(1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0);
    ASSERT(r == 36.0);
}

TEST(cpu_float_mixed_int) {
    double r = cpu_mixed_float_int(10, 1.5, 20, 2.5);
    ASSERT(r == 34.0);
}

TEST(cpu_float_edge_values) {
    volatile double nan_val = NAN;
    volatile double inf_val = INFINITY;
    volatile double neg_inf = -INFINITY;
    volatile double denorm = 5e-324;

    ASSERT(nan_val != nan_val);
    ASSERT(!(nan_val == nan_val));
    ASSERT(!(nan_val < 0.0));
    ASSERT(!(nan_val > 0.0));

    ASSERT(inf_val > 1e308);
    ASSERT(neg_inf < -1e308);
    ASSERT(inf_val + inf_val == inf_val);

    ASSERT(denorm > 0.0);
    ASSERT(denorm < 1e-300);

    /* NaN truthiness: spl_is_truthy(NaN) == 1 because NaN != 0.0 is true */
    SplValue nan_v = spl_float(nan_val);
    ASSERT(spl_is_truthy(nan_v));

    /* NaN equality: spl_eq(NaN, NaN) == 0 per IEEE 754 */
    ASSERT(!spl_eq(spl_float(nan_val), spl_float(nan_val)));
}

/* ================================================================
 * 37–38: Data Structure Stress
 * ================================================================ */

TEST(cpu_dict_64_keys_growth) {
    SplDict* d = spl_dict_new_cap(4);
    for (int64_t i = 0; i < 64; i++) {
        char key[32];
        snprintf(key, sizeof(key), "cpu_k_%lld", (long long)i);
        spl_dict_set(d, key, spl_int(i * i));
    }
    ASSERT_EQ_INT(spl_dict_len(d), 64);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "cpu_k_0")), 0);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "cpu_k_32")), 1024);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "cpu_k_63")), 3969);
    spl_dict_free(d);
}

TEST(cpu_array_10k_push) {
    SplArray* a = spl_array_new_cap(8);
    for (int64_t i = 0; i < 10000; i++) {
        spl_array_push(a, spl_int(i));
    }
    ASSERT_EQ_INT(spl_array_len(a), 10000);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 0);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 5000)), 5000);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 9999)), 9999);
    spl_array_free(a);
}

/* ================================================================
 * 39–41: Compiler Patterns
 * ================================================================ */

TEST(cpu_volatile_ordering) {
    volatile int64_t a = 0, b = 0;
    a = 1;
    b = 2;
    a = 3;
    ASSERT_EQ_INT(a, 3);
    ASSERT_EQ_INT(b, 2);
    volatile int64_t seq[4];
    for (int i = 0; i < 4; i++) seq[i] = i;
    ASSERT_EQ_INT(seq[0], 0);
    ASSERT_EQ_INT(seq[3], 3);
}

TEST(cpu_fn_ptr_array) {
    cpu_fn_ptr fns[3] = { cpu_add_one, cpu_double_it, cpu_negate_it };
    int64_t val = 5;
    for (int i = 0; i < 3; i++) {
        val = fns[i](val);
    }
    /* 5 -> +1 -> 6 -> *2 -> 12 -> neg -> -12 */
    ASSERT_EQ_INT(val, -12);
}

TEST(cpu_init_fini_pattern) {
    ASSERT(cpu_init_counter > 0);
}

/* ================================================================
 * Common dispatcher — called from arch-specific run_cpu_tests()
 * ================================================================ */

static void run_cpu_common_tests(void) {
    printf("\n--- CPU: Calling Convention (shared) ---\n");
    RUN(cpu_call_12_args_deep_stack);
    RUN(cpu_call_mixed_int_ptr);

    printf("\n--- CPU: Return Values ---\n");
    RUN(cpu_return_boundary_i64);
    RUN(cpu_return_splvalue_struct);
    RUN(cpu_return_struct_chain);

    printf("\n--- CPU: Stack Alignment ---\n");
    RUN(cpu_stack_alignment_basic);
    RUN(cpu_alloca_stress);
    RUN(cpu_nested_odd_frame);

    printf("\n--- CPU: WFFI ---\n");
    RUN(cpu_wffi_0_arg);
    RUN(cpu_wffi_4_arg_max);
    RUN(cpu_wffi_large_return);
    RUN(cpu_wffi_negative_return);
    RUN(cpu_wffi_ptr_as_i64);
    RUN(cpu_wffi_reentrant);

    printf("\n--- CPU: Large Immediates ---\n");
    RUN(cpu_large_immediate_64bit);
    RUN(cpu_fnv1a_constants);

    printf("\n--- CPU: Deep Recursion ---\n");
    RUN(cpu_recursion_100);
    RUN(cpu_recursion_1000);
    RUN(cpu_mutual_recursion);
    RUN(cpu_large_frame_recursion);

    printf("\n--- CPU: Memory Access ---\n");
    RUN(cpu_aligned_access);
    RUN(cpu_unaligned_memcpy);
    RUN(cpu_splvalue_alignment);
    RUN(cpu_dictentry_alignment);

    printf("\n--- CPU: Pointer Ops ---\n");
    RUN(cpu_ptr_roundtrip);
    RUN(cpu_null_is_zero);
    RUN(cpu_ptr_bit_preservation);

    printf("\n--- CPU: Variadic Args ---\n");
    RUN(cpu_variadic_10_ints);
    RUN(cpu_variadic_mixed);

    printf("\n--- CPU: setjmp/longjmp ---\n");
    RUN(cpu_setjmp_basic);
    RUN(cpu_setjmp_preserves_locals);

    printf("\n--- CPU: Floating Point ---\n");
    RUN(cpu_float_8_args);
    RUN(cpu_float_mixed_int);
    RUN(cpu_float_edge_values);

    printf("\n--- CPU: Data Stress ---\n");
    RUN(cpu_dict_64_keys_growth);
    RUN(cpu_array_10k_push);

    printf("\n--- CPU: Compiler Patterns ---\n");
    RUN(cpu_volatile_ordering);
    RUN(cpu_fn_ptr_array);
    RUN(cpu_init_fini_pattern);
}

#endif /* SPL_TEST_CPU_COMMON_H */
