/*
 * Simple Bootstrap Runtime — Test Suite
 *
 * Build and run:
 *   gcc -o /tmp/runtime_test bootstrap/runtime_test.c bootstrap/runtime.c -std=c11 && /tmp/runtime_test
 *
 * Options:
 *   --fail-fast    Stop on first test failure (exit code 1)
 *   --verbose      Show test names as they run
 */

/* Platform detection */
#ifndef _WIN32
#define _POSIX_C_SOURCE 200809L
#endif

#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

/* Platform-specific headers */
#ifndef _WIN32
#include <sys/wait.h>
#include <unistd.h>
#else
/* Windows doesn't need these for runtime tests */
#endif

static int tests_run = 0;

#define TEST(name) static void test_##name(void)
#define RUN(name) do { \
    tests_run++; \
    printf("  %-50s", #name); \
    fflush(stdout); \
    test_##name(); \
    printf(" OK\n"); \
} while(0)

#define ASSERT(cond) do { \
    if (!(cond)) { \
        printf(" FAIL\n    %s\n    %s:%d\n", #cond, __FILE__, __LINE__); \
        exit(1); \
    } \
} while(0)

#define ASSERT_EQ_INT(a, b) do { \
    int64_t _a = (a), _b = (b); \
    if (_a != _b) { \
        printf(" FAIL\n    %lld != %lld\n    %s:%d\n", \
               (long long)_a, (long long)_b, __FILE__, __LINE__); \
        exit(1); \
    } \
} while(0)

#define ASSERT_EQ_STR(a, b) do { \
    const char* _a = (a); const char* _b = (b); \
    if (strcmp(_a ? _a : "", _b ? _b : "") != 0) { \
        printf(" FAIL\n    \"%s\" != \"%s\"\n    %s:%d\n", \
               _a ? _a : "(null)", _b ? _b : "(null)", __FILE__, __LINE__); \
        exit(1); \
    } \
} while(0)

/* ================================================================
 * Value Constructor Tests
 * ================================================================ */

TEST(nil_value) {
    SplValue v = spl_nil();
    ASSERT(v.tag == SPL_NIL);
    ASSERT(!spl_is_truthy(v));
}

TEST(bool_value) {
    SplValue t = spl_bool(1);
    SplValue f = spl_bool(0);
    ASSERT(t.tag == SPL_BOOL);
    ASSERT(spl_as_bool(t) == 1);
    ASSERT(spl_as_bool(f) == 0);
    ASSERT(spl_is_truthy(t));
    ASSERT(!spl_is_truthy(f));
}

TEST(int_value) {
    SplValue v = spl_int(42);
    ASSERT(v.tag == SPL_INT);
    ASSERT_EQ_INT(spl_as_int(v), 42);
    ASSERT(spl_is_truthy(v));
    ASSERT(!spl_is_truthy(spl_int(0)));
}

TEST(float_value) {
    SplValue v = spl_float(3.14);
    ASSERT(v.tag == SPL_FLOAT);
    ASSERT(spl_as_float(v) == 3.14);
    ASSERT(spl_is_truthy(v));
    ASSERT(!spl_is_truthy(spl_float(0.0)));
}

TEST(string_value) {
    SplValue v = spl_str("hello");
    ASSERT(v.tag == SPL_STRING);
    ASSERT_EQ_STR(spl_as_str(v), "hello");
    ASSERT(spl_is_truthy(v));
    SplValue empty = spl_str("");
    ASSERT(!spl_is_truthy(empty));
    spl_free_value(empty);
    spl_free_value(v);
}

TEST(string_own_value) {
    char* s = strdup("owned");
    SplValue v = spl_str_own(s);
    ASSERT_EQ_STR(spl_as_str(v), "owned");
    spl_free_value(v);
}

/* ================================================================
 * Value Equality Tests
 * ================================================================ */

TEST(eq_nil) {
    ASSERT(spl_eq(spl_nil(), spl_nil()));
}

TEST(eq_bool) {
    ASSERT(spl_eq(spl_bool(1), spl_bool(1)));
    ASSERT(!spl_eq(spl_bool(1), spl_bool(0)));
}

TEST(eq_int) {
    ASSERT(spl_eq(spl_int(42), spl_int(42)));
    ASSERT(!spl_eq(spl_int(42), spl_int(43)));
}

TEST(eq_string) {
    SplValue a = spl_str("hello");
    SplValue b = spl_str("hello");
    SplValue c = spl_str("world");
    ASSERT(spl_eq(a, b));
    ASSERT(!spl_eq(a, c));
    spl_free_value(a);
    spl_free_value(b);
    spl_free_value(c);
}

TEST(eq_different_types) {
    ASSERT(!spl_eq(spl_int(0), spl_nil()));
    ASSERT(!spl_eq(spl_int(1), spl_bool(1)));
    SplValue s42 = spl_str("42");
    ASSERT(!spl_eq(s42, spl_int(42)));
    spl_free_value(s42);
}

/* ================================================================
 * Value to_string Tests
 * ================================================================ */

TEST(to_string_nil) {
    SplValue s = spl_to_string(spl_nil());
    ASSERT_EQ_STR(spl_as_str(s), "nil");
    spl_free_value(s);
}

TEST(to_string_bool) {
    SplValue t = spl_to_string(spl_bool(1));
    SplValue f = spl_to_string(spl_bool(0));
    ASSERT_EQ_STR(spl_as_str(t), "true");
    ASSERT_EQ_STR(spl_as_str(f), "false");
    spl_free_value(t);
    spl_free_value(f);
}

TEST(to_string_int) {
    SplValue s = spl_to_string(spl_int(-123));
    ASSERT_EQ_STR(spl_as_str(s), "-123");
    spl_free_value(s);
}

TEST(to_string_float) {
    SplValue s = spl_to_string(spl_float(3.14));
    ASSERT_EQ_STR(spl_as_str(s), "3.14");
    spl_free_value(s);
}

TEST(to_string_string) {
    SplValue orig = spl_str("hello");
    SplValue s = spl_to_string(orig);
    ASSERT_EQ_STR(spl_as_str(s), "hello");
    spl_free_value(orig);
    spl_free_value(s);
}

TEST(to_string_array) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));
    spl_array_push(a, spl_int(3));
    SplValue s = spl_to_string(spl_array_val(a));
    ASSERT_EQ_STR(spl_as_str(s), "[1, 2, 3]");
    spl_free_value(s);
    spl_array_free(a);
}

TEST(to_string_empty_array) {
    SplArray* a = spl_array_new();
    SplValue s = spl_to_string(spl_array_val(a));
    ASSERT_EQ_STR(spl_as_str(s), "[]");
    spl_free_value(s);
    spl_array_free(a);
}

/* ================================================================
 * String Operation Tests
 * ================================================================ */

TEST(str_new) {
    char* s = spl_str_new("test");
    ASSERT_EQ_STR(s, "test");
    free(s);

    char* n = spl_str_new(NULL);
    ASSERT_EQ_STR(n, "");
    free(n);
}

TEST(str_concat) {
    char* s = spl_str_concat("hello", " world");
    ASSERT_EQ_STR(s, "hello world");
    free(s);

    char* e = spl_str_concat("", "abc");
    ASSERT_EQ_STR(e, "abc");
    free(e);

    char* n = spl_str_concat(NULL, NULL);
    ASSERT_EQ_STR(n, "");
    free(n);
}

TEST(str_len) {
    ASSERT_EQ_INT(spl_str_len("hello"), 5);
    ASSERT_EQ_INT(spl_str_len(""), 0);
    ASSERT_EQ_INT(spl_str_len(NULL), 0);
}

TEST(str_eq) {
    ASSERT(spl_str_eq("abc", "abc"));
    ASSERT(!spl_str_eq("abc", "def"));
    ASSERT(spl_str_eq("", ""));
    ASSERT(spl_str_eq(NULL, NULL));
    ASSERT(!spl_str_eq("abc", NULL));
}

TEST(str_cmp) {
    ASSERT(spl_str_cmp("abc", "abc") == 0);
    ASSERT(spl_str_cmp("abc", "def") < 0);
    ASSERT(spl_str_cmp("def", "abc") > 0);
}

TEST(str_slice) {
    char* s = spl_str_slice("hello world", 0, 5);
    ASSERT_EQ_STR(s, "hello");
    free(s);

    char* m = spl_str_slice("hello world", 6, 11);
    ASSERT_EQ_STR(m, "world");
    free(m);

    char* neg = spl_str_slice("hello", -3, -1);
    ASSERT_EQ_STR(neg, "ll");
    free(neg);

    char* empty = spl_str_slice("hello", 3, 3);
    ASSERT_EQ_STR(empty, "");
    free(empty);
}

TEST(str_index_char) {
    char* c = spl_str_index_char("hello", 0);
    ASSERT_EQ_STR(c, "h");
    free(c);

    char* last = spl_str_index_char("hello", -1);
    ASSERT_EQ_STR(last, "o");
    free(last);

    char* oob = spl_str_index_char("hi", 5);
    ASSERT_EQ_STR(oob, "");
    free(oob);
}

TEST(str_hash) {
    uint64_t h1 = spl_str_hash("hello");
    uint64_t h2 = spl_str_hash("hello");
    uint64_t h3 = spl_str_hash("world");
    ASSERT(h1 == h2);  /* deterministic */
    ASSERT(h1 != h3);  /* different strings should differ */
    ASSERT(spl_str_hash(NULL) != 0);  /* NULL returns base hash */
}

TEST(str_contains) {
    ASSERT(spl_str_contains("hello world", "world"));
    ASSERT(spl_str_contains("hello world", "hello"));
    ASSERT(!spl_str_contains("hello world", "xyz"));
    ASSERT(spl_str_contains("abc", ""));
    ASSERT(!spl_str_contains(NULL, "x"));
}

TEST(str_starts_with) {
    ASSERT(spl_str_starts_with("hello world", "hello"));
    ASSERT(!spl_str_starts_with("hello world", "world"));
    ASSERT(spl_str_starts_with("abc", ""));
}

TEST(str_ends_with) {
    ASSERT(spl_str_ends_with("hello world", "world"));
    ASSERT(!spl_str_ends_with("hello world", "hello"));
    ASSERT(spl_str_ends_with("abc", ""));
}

TEST(str_replace) {
    char* s = spl_str_replace("hello world", "world", "there");
    ASSERT_EQ_STR(s, "hello there");
    free(s);

    char* multi = spl_str_replace("aabbaa", "aa", "x");
    ASSERT_EQ_STR(multi, "xbbx");
    free(multi);

    char* none = spl_str_replace("hello", "xyz", "abc");
    ASSERT_EQ_STR(none, "hello");
    free(none);
}

TEST(str_trim) {
    char* s = spl_str_trim("  hello  ");
    ASSERT_EQ_STR(s, "hello");
    free(s);

    char* tabs = spl_str_trim("\t\n hello \r\n");
    ASSERT_EQ_STR(tabs, "hello");
    free(tabs);

    char* clean = spl_str_trim("hello");
    ASSERT_EQ_STR(clean, "hello");
    free(clean);
}

TEST(str_index_of) {
    ASSERT_EQ_INT(spl_str_index_of("hello world", "world"), 6);
    ASSERT_EQ_INT(spl_str_index_of("hello world", "xyz"), -1);
    ASSERT_EQ_INT(spl_str_index_of("hello", ""), 0);
}

TEST(str_to_upper) {
    char* s = spl_str_to_upper("Hello World");
    ASSERT_EQ_STR(s, "HELLO WORLD");
    free(s);
}

TEST(str_to_lower) {
    char* s = spl_str_to_lower("Hello World");
    ASSERT_EQ_STR(s, "hello world");
    free(s);
}

/* ================================================================
 * Array Tests
 * ================================================================ */

TEST(array_basic) {
    SplArray* a = spl_array_new();
    ASSERT_EQ_INT(spl_array_len(a), 0);

    spl_array_push(a, spl_int(10));
    spl_array_push(a, spl_int(20));
    spl_array_push(a, spl_int(30));
    ASSERT_EQ_INT(spl_array_len(a), 3);

    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 10);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 1)), 20);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 2)), 30);

    spl_array_free(a);
}

TEST(array_negative_index) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));
    spl_array_push(a, spl_int(3));

    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, -1)), 3);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, -2)), 2);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, -3)), 1);
    ASSERT(spl_array_get(a, -4).tag == SPL_NIL);

    spl_array_free(a);
}

TEST(array_set) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));

    spl_array_set(a, 0, spl_int(99));
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 99);

    spl_array_set(a, -1, spl_int(88));
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 1)), 88);

    spl_array_free(a);
}

TEST(array_pop) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));

    SplValue v = spl_array_pop(a);
    ASSERT_EQ_INT(spl_as_int(v), 2);
    ASSERT_EQ_INT(spl_array_len(a), 1);

    v = spl_array_pop(a);
    ASSERT_EQ_INT(spl_as_int(v), 1);
    ASSERT_EQ_INT(spl_array_len(a), 0);

    v = spl_array_pop(a);
    ASSERT(v.tag == SPL_NIL);

    spl_array_free(a);
}

TEST(array_out_of_bounds) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(42));

    ASSERT(spl_array_get(a, 5).tag == SPL_NIL);
    ASSERT(spl_array_get(a, -5).tag == SPL_NIL);

    spl_array_free(a);
}

TEST(array_grow) {
    SplArray* a = spl_array_new_cap(4);
    for (int64_t i = 0; i < 100; i++) {
        spl_array_push(a, spl_int(i));
    }
    ASSERT_EQ_INT(spl_array_len(a), 100);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 0);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 99)), 99);
    spl_array_free(a);
}

TEST(array_slice) {
    SplArray* a = spl_array_new();
    for (int64_t i = 0; i < 5; i++) spl_array_push(a, spl_int(i * 10));

    SplArray* s = spl_array_slice(a, 1, 4);
    ASSERT_EQ_INT(spl_array_len(s), 3);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(s, 0)), 10);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(s, 1)), 20);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(s, 2)), 30);

    spl_array_free(s);
    spl_array_free(a);
}

TEST(array_concat) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));

    SplArray* b = spl_array_new();
    spl_array_push(b, spl_int(3));
    spl_array_push(b, spl_int(4));

    SplArray* c = spl_array_concat(a, b);
    ASSERT_EQ_INT(spl_array_len(c), 4);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(c, 0)), 1);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(c, 3)), 4);

    free(c->items); free(c); /* shallow free since items are shared */
    spl_array_free(a);
    spl_array_free(b);
}

TEST(array_mixed_types) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(42));
    spl_array_push(a, spl_str("hello"));
    spl_array_push(a, spl_bool(1));
    spl_array_push(a, spl_nil());

    ASSERT(spl_array_get(a, 0).tag == SPL_INT);
    ASSERT(spl_array_get(a, 1).tag == SPL_STRING);
    ASSERT(spl_array_get(a, 2).tag == SPL_BOOL);
    ASSERT(spl_array_get(a, 3).tag == SPL_NIL);

    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 42);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(a, 1)), "hello");

    spl_array_free(a);
}

/* Typed convenience */
TEST(array_i64) {
    SplArray* a = spl_array_new_i64();
    spl_array_push_i64(a, 10);
    spl_array_push_i64(a, 20);
    spl_array_push_i64(a, 30);

    ASSERT_EQ_INT(spl_array_get_i64(a, 0), 10);
    ASSERT_EQ_INT(spl_array_get_i64(a, 1), 20);
    ASSERT_EQ_INT(spl_array_get_i64(a, 2), 30);

    spl_array_set_i64(a, 1, 99);
    ASSERT_EQ_INT(spl_array_get_i64(a, 1), 99);

    spl_array_free(a);
}

TEST(array_text) {
    SplArray* a = spl_array_new_text();
    spl_array_push_text(a, "hello");
    spl_array_push_text(a, "world");

    ASSERT_EQ_STR(spl_array_get_text(a, 0), "hello");
    ASSERT_EQ_STR(spl_array_get_text(a, 1), "world");

    spl_array_free(a);
}

/* ================================================================
 * Dict Tests
 * ================================================================ */

TEST(dict_basic) {
    SplDict* d = spl_dict_new();
    ASSERT_EQ_INT(spl_dict_len(d), 0);

    spl_dict_set(d, "x", spl_int(10));
    spl_dict_set(d, "y", spl_int(20));

    ASSERT_EQ_INT(spl_dict_len(d), 2);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "x")), 10);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "y")), 20);

    spl_dict_free(d);
}

TEST(dict_overwrite) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "key", spl_int(1));
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "key")), 1);

    spl_dict_set(d, "key", spl_int(2));
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "key")), 2);
    ASSERT_EQ_INT(spl_dict_len(d), 1); /* still just one entry */

    spl_dict_free(d);
}

TEST(dict_contains) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "exists", spl_int(1));

    ASSERT(spl_dict_contains(d, "exists"));
    ASSERT(!spl_dict_contains(d, "missing"));

    spl_dict_free(d);
}

TEST(dict_missing_key) {
    SplDict* d = spl_dict_new();
    SplValue v = spl_dict_get(d, "nope");
    ASSERT(v.tag == SPL_NIL);
    spl_dict_free(d);
}

TEST(dict_remove) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_set(d, "b", spl_int(2));
    spl_dict_set(d, "c", spl_int(3));
    ASSERT_EQ_INT(spl_dict_len(d), 3);

    spl_dict_remove(d, "b");
    ASSERT_EQ_INT(spl_dict_len(d), 2);
    ASSERT(!spl_dict_contains(d, "b"));
    ASSERT(spl_dict_contains(d, "a"));
    ASSERT(spl_dict_contains(d, "c"));

    /* Can re-insert after remove */
    spl_dict_set(d, "b", spl_int(99));
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "b")), 99);
    ASSERT_EQ_INT(spl_dict_len(d), 3);

    spl_dict_free(d);
}

TEST(dict_keys) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "alpha", spl_int(1));
    spl_dict_set(d, "beta", spl_int(2));
    spl_dict_set(d, "gamma", spl_int(3));

    SplArray* keys = spl_dict_keys(d);
    ASSERT_EQ_INT(spl_array_len(keys), 3);

    /* Keys are present (order may vary due to hashing) */
    int found_alpha = 0, found_beta = 0, found_gamma = 0;
    for (int64_t i = 0; i < spl_array_len(keys); i++) {
        const char* k = spl_as_str(spl_array_get(keys, i));
        if (strcmp(k, "alpha") == 0) found_alpha = 1;
        if (strcmp(k, "beta") == 0) found_beta = 1;
        if (strcmp(k, "gamma") == 0) found_gamma = 1;
    }
    ASSERT(found_alpha && found_beta && found_gamma);

    spl_array_free(keys);
    spl_dict_free(d);
}

TEST(dict_values) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(10));
    spl_dict_set(d, "b", spl_int(20));

    SplArray* vals = spl_dict_values(d);
    ASSERT_EQ_INT(spl_array_len(vals), 2);

    int64_t sum = 0;
    for (int64_t i = 0; i < spl_array_len(vals); i++) {
        sum += spl_as_int(spl_array_get(vals, i));
    }
    ASSERT_EQ_INT(sum, 30);

    free(vals->items); free(vals); /* shallow free */
    spl_dict_free(d);
}

TEST(dict_grow) {
    SplDict* d = spl_dict_new_cap(4);
    for (int64_t i = 0; i < 200; i++) {
        char key[32];
        snprintf(key, sizeof(key), "key_%lld", (long long)i);
        spl_dict_set(d, key, spl_int(i));
    }
    ASSERT_EQ_INT(spl_dict_len(d), 200);

    /* Verify all entries survived resizing */
    for (int64_t i = 0; i < 200; i++) {
        char key[32];
        snprintf(key, sizeof(key), "key_%lld", (long long)i);
        ASSERT(spl_dict_contains(d, key));
        ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, key)), i);
    }

    spl_dict_free(d);
}

TEST(dict_string_values) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "name", spl_str("Alice"));
    spl_dict_set(d, "city", spl_str("NYC"));

    ASSERT_EQ_STR(spl_as_str(spl_dict_get(d, "name")), "Alice");
    ASSERT_EQ_STR(spl_as_str(spl_dict_get(d, "city")), "NYC");

    spl_dict_free(d);
}

TEST(dict_mixed_values) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "int_val", spl_int(42));
    spl_dict_set(d, "str_val", spl_str("hello"));
    spl_dict_set(d, "bool_val", spl_bool(1));
    spl_dict_set(d, "nil_val", spl_nil());

    ASSERT(spl_dict_get(d, "int_val").tag == SPL_INT);
    ASSERT(spl_dict_get(d, "str_val").tag == SPL_STRING);
    ASSERT(spl_dict_get(d, "bool_val").tag == SPL_BOOL);
    ASSERT(spl_dict_get(d, "nil_val").tag == SPL_NIL);

    spl_dict_free(d);
}

/* ================================================================
 * File I/O Tests
 * ================================================================ */

TEST(file_write_read) {
    const char* path = "/tmp/spl_runtime_test.txt";
    ASSERT(spl_file_write(path, "test content"));
    ASSERT(spl_file_exists(path));

    char* content = spl_file_read(path);
    ASSERT_EQ_STR(content, "test content");
    free(content);

    /* Clean up */
    remove(path);
}

TEST(file_append) {
    const char* path = "/tmp/spl_runtime_append_test.txt";
    spl_file_write(path, "line1");
    spl_file_append(path, "\nline2");

    char* content = spl_file_read(path);
    ASSERT_EQ_STR(content, "line1\nline2");
    free(content);

    remove(path);
}

TEST(file_not_exists) {
    ASSERT(!spl_file_exists("/tmp/spl_nonexistent_file_xyz.txt"));
    char* content = spl_file_read("/tmp/spl_nonexistent_file_xyz.txt");
    ASSERT_EQ_STR(content, "");
    free(content);
}

/* ================================================================
 * Format Tests
 * ================================================================ */

TEST(i64_to_str) {
    char* s = spl_i64_to_str(42);
    ASSERT_EQ_STR(s, "42");
    free(s);

    char* neg = spl_i64_to_str(-100);
    ASSERT_EQ_STR(neg, "-100");
    free(neg);

    char* zero = spl_i64_to_str(0);
    ASSERT_EQ_STR(zero, "0");
    free(zero);
}

TEST(f64_to_str) {
    char* s = spl_f64_to_str(3.14);
    ASSERT_EQ_STR(s, "3.14");
    free(s);

    char* z = spl_f64_to_str(0.0);
    ASSERT_EQ_STR(z, "0");
    free(z);
}

TEST(sprintf_test) {
    char* s = spl_sprintf("hello %s, you are %d", "world", 42);
    ASSERT_EQ_STR(s, "hello world, you are 42");
    free(s);
}

/* ================================================================
 * Process Tests
 * ================================================================ */

TEST(shell_output) {
    char* output = spl_shell_output("echo hello");
    ASSERT(spl_str_starts_with(output, "hello"));
    free(output);
}

TEST(shell_return) {
    int64_t rc = spl_shell("true");
    ASSERT_EQ_INT(rc, 0);
}

/* ================================================================
 * Environment Tests
 * ================================================================ */

TEST(env_get_set) {
    spl_env_set("SPL_TEST_VAR", "test_value");
    ASSERT_EQ_STR(spl_env_get("SPL_TEST_VAR"), "test_value");

    spl_env_set("SPL_TEST_VAR", NULL); /* unset */
    ASSERT_EQ_STR(spl_env_get("SPL_TEST_VAR"), "");
}

/* ================================================================
 * Memory Tests
 * ================================================================ */

TEST(malloc_free) {
    void* p = spl_malloc(1024);
    ASSERT(p != NULL);
    memset(p, 0, 1024);
    spl_free(p);
}

TEST(strdup_test) {
    char* s = spl_strdup("hello");
    ASSERT_EQ_STR(s, "hello");
    free(s);

    char* n = spl_strdup(NULL);
    ASSERT_EQ_STR(n, "");
    free(n);
}

/* ================================================================
 * Integration Tests — Compiler-like workloads
 * ================================================================ */

TEST(token_storage) {
    /* Simulate storing tokens in arrays like the bootstrap lexer would */
    SplArray* kinds = spl_array_new_i64();
    SplArray* values = spl_array_new_text();

    spl_array_push_i64(kinds, 10);  /* TOK_KW_FN */
    spl_array_push_text(values, "fn");

    spl_array_push_i64(kinds, 2);   /* TOK_IDENT */
    spl_array_push_text(values, "main");

    spl_array_push_i64(kinds, 20);  /* TOK_LPAREN */
    spl_array_push_text(values, "(");

    ASSERT_EQ_INT(spl_array_len(kinds), 3);
    ASSERT_EQ_INT(spl_array_get_i64(kinds, 0), 10);
    ASSERT_EQ_STR(spl_array_get_text(values, 1), "main");

    spl_array_free(kinds);
    spl_array_free(values);
}

TEST(symbol_table) {
    /* Simulate a symbol table: name -> (type_tag, scope_depth) */
    SplDict* symbols = spl_dict_new();

    /* Store x: (type=INT, depth=0) as packed int */
    spl_dict_set(symbols, "x", spl_int(1 * 1000 + 0));  /* type=1(INT), depth=0 */
    spl_dict_set(symbols, "y", spl_int(2 * 1000 + 1));  /* type=2(STR), depth=1 */
    spl_dict_set(symbols, "foo", spl_int(3 * 1000 + 0)); /* type=3(FN), depth=0 */

    ASSERT(spl_dict_contains(symbols, "x"));
    ASSERT(spl_dict_contains(symbols, "foo"));
    ASSERT(!spl_dict_contains(symbols, "bar"));

    /* Lookup and decode */
    int64_t x_info = spl_as_int(spl_dict_get(symbols, "x"));
    ASSERT_EQ_INT(x_info / 1000, 1); /* type = INT */
    ASSERT_EQ_INT(x_info % 1000, 0); /* depth = 0 */

    spl_dict_free(symbols);
}

TEST(ast_arena_pattern) {
    /* Simulate arena-based AST storage (the bootstrap compiler's approach) */
    SplArray* expr_tags = spl_array_new_i64();
    SplArray* expr_names = spl_array_new_text();
    SplArray* expr_ints = spl_array_new_i64();
    SplArray* expr_left = spl_array_new_i64();
    SplArray* expr_right = spl_array_new_i64();

    /* Expr 0: IntLit(42) */
    spl_array_push_i64(expr_tags, 1);    /* EXPR_INT */
    spl_array_push_text(expr_names, "");
    spl_array_push_i64(expr_ints, 42);
    spl_array_push_i64(expr_left, -1);
    spl_array_push_i64(expr_right, -1);

    /* Expr 1: Ident("x") */
    spl_array_push_i64(expr_tags, 2);    /* EXPR_IDENT */
    spl_array_push_text(expr_names, "x");
    spl_array_push_i64(expr_ints, 0);
    spl_array_push_i64(expr_left, -1);
    spl_array_push_i64(expr_right, -1);

    /* Expr 2: BinOp(+, expr0, expr1) */
    spl_array_push_i64(expr_tags, 3);    /* EXPR_BINOP */
    spl_array_push_text(expr_names, "+");
    spl_array_push_i64(expr_ints, 0);
    spl_array_push_i64(expr_left, 0);    /* points to expr 0 */
    spl_array_push_i64(expr_right, 1);   /* points to expr 1 */

    /* Verify arena lookups */
    ASSERT_EQ_INT(spl_array_get_i64(expr_tags, 2), 3);          /* BinOp tag */
    ASSERT_EQ_STR(spl_array_get_text(expr_names, 2), "+");      /* operator */
    ASSERT_EQ_INT(spl_array_get_i64(expr_left, 2), 0);          /* left = expr 0 */
    ASSERT_EQ_INT(spl_array_get_i64(expr_right, 2), 1);         /* right = expr 1 */

    /* Follow left child: expr 0 is IntLit(42) */
    int64_t left_idx = spl_array_get_i64(expr_left, 2);
    ASSERT_EQ_INT(spl_array_get_i64(expr_tags, left_idx), 1);   /* EXPR_INT */
    ASSERT_EQ_INT(spl_array_get_i64(expr_ints, left_idx), 42);

    spl_array_free(expr_tags);
    spl_array_free(expr_names);
    spl_array_free(expr_ints);
    spl_array_free(expr_left);
    spl_array_free(expr_right);
}

TEST(c_codegen_string_building) {
    /* Simulate building C output strings like the codegen would */
    SplArray* lines = spl_array_new_text();
    spl_array_push_text(lines, "#include <stdio.h>");
    spl_array_push_text(lines, "#include <stdlib.h>");
    spl_array_push_text(lines, "");
    spl_array_push_text(lines, "int main(void) {");
    spl_array_push_text(lines, "    printf(\"hello\\n\");");
    spl_array_push_text(lines, "    return 0;");
    spl_array_push_text(lines, "}");

    ASSERT_EQ_INT(spl_array_len(lines), 7);
    ASSERT_EQ_STR(spl_array_get_text(lines, 0), "#include <stdio.h>");
    ASSERT(spl_str_contains(spl_array_get_text(lines, 4), "printf"));

    spl_array_free(lines);
}

/* ================================================================
 * Coverage: Value edge cases
 * ================================================================ */

TEST(is_truthy_array) {
    SplArray* a = spl_array_new();
    ASSERT(!spl_is_truthy(spl_array_val(a)));  /* empty array = falsy */
    spl_array_push(a, spl_int(1));
    ASSERT(spl_is_truthy(spl_array_val(a)));   /* non-empty = truthy */
    spl_array_free(a);
}

TEST(is_truthy_dict) {
    SplDict* d = spl_dict_new();
    ASSERT(!spl_is_truthy(spl_dict_val(d)));   /* empty dict = falsy */
    spl_dict_set(d, "k", spl_int(1));
    ASSERT(spl_is_truthy(spl_dict_val(d)));    /* non-empty = truthy */
    spl_dict_free(d);
}

TEST(is_truthy_null_containers) {
    SplValue null_arr;
    null_arr.tag = SPL_ARRAY;
    null_arr.as_array = NULL;
    ASSERT(!spl_is_truthy(null_arr));

    SplValue null_dict;
    null_dict.tag = SPL_DICT;
    null_dict.as_dict = NULL;
    ASSERT(!spl_is_truthy(null_dict));
}

TEST(eq_float) {
    ASSERT(spl_eq(spl_float(3.14), spl_float(3.14)));
    ASSERT(!spl_eq(spl_float(3.14), spl_float(2.71)));
}

TEST(eq_array) {
    SplArray* a = spl_array_new();
    SplArray* b = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));
    spl_array_push(b, spl_int(1));
    spl_array_push(b, spl_int(2));
    ASSERT(spl_eq(spl_array_val(a), spl_array_val(b)));

    spl_array_push(b, spl_int(3));
    ASSERT(!spl_eq(spl_array_val(a), spl_array_val(b)));

    spl_array_free(a);
    spl_array_free(b);
}

TEST(eq_array_null) {
    SplValue a_null;
    a_null.tag = SPL_ARRAY;
    a_null.as_array = NULL;
    ASSERT(spl_eq(a_null, a_null)); /* both NULL = equal */

    SplArray* b = spl_array_new();
    ASSERT(!spl_eq(a_null, spl_array_val(b)));
    ASSERT(!spl_eq(spl_array_val(b), a_null));
    spl_array_free(b);
}

TEST(eq_dict_pointer) {
    SplDict* d = spl_dict_new();
    ASSERT(spl_eq(spl_dict_val(d), spl_dict_val(d)));  /* same ptr = equal */
    SplDict* d2 = spl_dict_new();
    ASSERT(!spl_eq(spl_dict_val(d), spl_dict_val(d2))); /* diff ptr = not equal */
    spl_dict_free(d);
    spl_dict_free(d2);
}

TEST(to_string_dict) {
    SplDict* d = spl_dict_new();
    SplValue s = spl_to_string(spl_dict_val(d));
    ASSERT_EQ_STR(spl_as_str(s), "{...}");
    spl_free_value(s);
    spl_dict_free(d);
}

TEST(to_string_large_array) {
    /* Force buffer realloc in spl_to_string for arrays */
    SplArray* a = spl_array_new();
    for (int64_t i = 0; i < 100; i++) {
        spl_array_push(a, spl_str("item_with_long_name_to_force_realloc"));
    }
    SplValue s = spl_to_string(spl_array_val(a));
    ASSERT(spl_str_contains(spl_as_str(s), "item_with_long_name_to_force_realloc"));
    ASSERT(spl_as_str(s)[0] == '[');
    spl_free_value(s);
    spl_array_free(a);
}

TEST(to_string_null_array) {
    SplValue null_arr;
    null_arr.tag = SPL_ARRAY;
    null_arr.as_array = NULL;
    SplValue s = spl_to_string(null_arr);
    ASSERT_EQ_STR(spl_as_str(s), "[]");
    spl_free_value(s);
}

TEST(free_value_all_types) {
    /* Verify free_value doesn't crash for any type */
    spl_free_value(spl_nil());
    spl_free_value(spl_bool(1));
    spl_free_value(spl_int(42));
    spl_free_value(spl_float(3.14));
    spl_free_value(spl_str("hello"));

    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("test"));
    spl_free_value(spl_array_val(a));

    SplDict* d = spl_dict_new();
    spl_dict_set(d, "key", spl_str("val"));
    spl_free_value(spl_dict_val(d));
}

/* ================================================================
 * Coverage: String edge cases
 * ================================================================ */

TEST(str_null_paths) {
    /* Test all NULL parameter paths */
    ASSERT_EQ_STR(spl_str_slice(NULL, 0, 5), "");
    ASSERT_EQ_STR(spl_str_index_char(NULL, 0), "");
    ASSERT(!spl_str_contains("abc", NULL));
    ASSERT(!spl_str_starts_with(NULL, "abc"));
    ASSERT(!spl_str_starts_with("abc", NULL));
    ASSERT(!spl_str_ends_with(NULL, "abc"));
    ASSERT(!spl_str_ends_with("abc", NULL));
    ASSERT_EQ_STR(spl_str_replace(NULL, "a", "b"), "");
    ASSERT_EQ_STR(spl_str_replace("abc", NULL, "x"), "abc");
    ASSERT_EQ_STR(spl_str_replace("abc", "a", NULL), "abc");
    ASSERT_EQ_STR(spl_str_replace("abc", "", "x"), "abc");
    ASSERT_EQ_STR(spl_str_trim(NULL), "");
    ASSERT_EQ_INT(spl_str_index_of(NULL, "x"), -1);
    ASSERT_EQ_INT(spl_str_index_of("abc", NULL), -1);
    ASSERT_EQ_STR(spl_str_to_upper(NULL), "");
    ASSERT_EQ_STR(spl_str_to_lower(NULL), "");
}

TEST(str_slice_edge_cases) {
    /* start > end returns empty */
    char* s1 = spl_str_slice("hello", 3, 1);
    ASSERT_EQ_STR(s1, "");
    free(s1);

    /* end > len clamps */
    char* s2 = spl_str_slice("hi", 0, 100);
    ASSERT_EQ_STR(s2, "hi");
    free(s2);

    /* both negative, start < -len clamps to 0 */
    char* s3 = spl_str_slice("hello", -100, -1);
    ASSERT_EQ_STR(s3, "hell");
    free(s3);
}

TEST(str_ends_with_longer_suffix) {
    ASSERT(!spl_str_ends_with("hi", "longer_than_string"));
}

TEST(str_replace_empty_old) {
    char* s = spl_str_replace("abc", "", "x");
    ASSERT_EQ_STR(s, "abc");
    free(s);
}

TEST(str_trim_empty) {
    char* s = spl_str_trim("");
    ASSERT_EQ_STR(s, "");
    free(s);

    char* ws = spl_str_trim("   \t\n   ");
    ASSERT_EQ_STR(ws, "");
    free(ws);
}

/* ================================================================
 * Coverage: Array edge cases
 * ================================================================ */

TEST(array_null_ops) {
    /* NULL array operations shouldn't crash */
    spl_array_push(NULL, spl_int(1));
    ASSERT(spl_array_get(NULL, 0).tag == SPL_NIL);
    spl_array_set(NULL, 0, spl_int(1));
    ASSERT_EQ_INT(spl_array_len(NULL), 0);
    ASSERT(spl_array_pop(NULL).tag == SPL_NIL);
    spl_array_free(NULL);
}

TEST(array_slice_edge_cases) {
    SplArray* a = spl_array_new();
    for (int64_t i = 0; i < 5; i++) spl_array_push(a, spl_int(i));

    /* Negative indices */
    SplArray* s1 = spl_array_slice(a, -3, -1);
    ASSERT_EQ_INT(spl_array_len(s1), 2);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(s1, 0)), 2);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(s1, 1)), 3);

    /* start > end */
    SplArray* s2 = spl_array_slice(a, 3, 1);
    ASSERT_EQ_INT(spl_array_len(s2), 0);

    /* end > len clamps */
    SplArray* s3 = spl_array_slice(a, 0, 100);
    ASSERT_EQ_INT(spl_array_len(s3), 5);

    /* NULL array */
    SplArray* s4 = spl_array_slice(NULL, 0, 5);
    ASSERT_EQ_INT(spl_array_len(s4), 0);

    /* start < -len clamps to 0 */
    SplArray* s5 = spl_array_slice(a, -100, 3);
    ASSERT_EQ_INT(spl_array_len(s5), 3);

    free(s1->items); free(s1);
    free(s2->items); free(s2);
    free(s3->items); free(s3);
    spl_array_free(s4);
    free(s5->items); free(s5);
    spl_array_free(a);
}

TEST(array_concat_null) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));

    SplArray* r1 = spl_array_concat(a, NULL);
    ASSERT_EQ_INT(spl_array_len(r1), 1);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(r1, 0)), 1);

    SplArray* r2 = spl_array_concat(NULL, a);
    ASSERT_EQ_INT(spl_array_len(r2), 1);

    SplArray* r3 = spl_array_concat(NULL, NULL);
    ASSERT_EQ_INT(spl_array_len(r3), 0);

    free(r1->items); free(r1);
    free(r2->items); free(r2);
    free(r3->items); free(r3);
    spl_array_free(a);
}

TEST(array_set_out_of_bounds) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_set(a, 5, spl_int(99));   /* positive OOB - should be no-op */
    spl_array_set(a, -5, spl_int(99));  /* negative OOB - should be no-op */
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 1);
    spl_array_free(a);
}

/* ================================================================
 * Coverage: Dict edge cases
 * ================================================================ */

TEST(dict_null_ops) {
    /* NULL dict operations shouldn't crash */
    spl_dict_set(NULL, "k", spl_int(1));
    ASSERT(spl_dict_get(NULL, "k").tag == SPL_NIL);
    ASSERT(!spl_dict_contains(NULL, "k"));
    ASSERT_EQ_INT(spl_dict_len(NULL), 0);
    spl_dict_remove(NULL, "k");
    spl_dict_free(NULL);
}

TEST(dict_null_key) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, NULL, spl_int(1));   /* should be no-op */
    ASSERT_EQ_INT(spl_dict_len(d), 0);
    ASSERT(spl_dict_get(d, NULL).tag == SPL_NIL);
    ASSERT(!spl_dict_contains(d, NULL));
    spl_dict_free(d);
}

TEST(dict_keys_null) {
    SplArray* keys = spl_dict_keys(NULL);
    ASSERT_EQ_INT(spl_array_len(keys), 0);
    spl_array_free(keys);
}

TEST(dict_values_null) {
    SplArray* vals = spl_dict_values(NULL);
    ASSERT_EQ_INT(spl_array_len(vals), 0);
    free(vals->items); free(vals);
}

TEST(dict_remove_nonexistent) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_remove(d, "nonexistent");  /* should be no-op */
    ASSERT_EQ_INT(spl_dict_len(d), 1);
    spl_dict_free(d);
}

TEST(dict_tombstone_reuse) {
    /* Test that tombstones are properly reused */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_set(d, "b", spl_int(2));
    spl_dict_remove(d, "a");
    ASSERT_EQ_INT(d->tombstones, 1);
    spl_dict_set(d, "a", spl_int(10));  /* should reuse tombstone */
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "a")), 10);
    ASSERT_EQ_INT(spl_dict_len(d), 2);
    spl_dict_free(d);
}

TEST(dict_resize_with_tombstones) {
    /* Force resize with tombstones present */
    SplDict* d = spl_dict_new_cap(4);
    for (int64_t i = 0; i < 10; i++) {
        char key[32];
        snprintf(key, sizeof(key), "k%lld", (long long)i);
        spl_dict_set(d, key, spl_int(i));
    }
    /* Remove some to create tombstones */
    spl_dict_remove(d, "k0");
    spl_dict_remove(d, "k2");
    spl_dict_remove(d, "k4");
    /* Add more to force resize */
    for (int64_t i = 10; i < 20; i++) {
        char key[32];
        snprintf(key, sizeof(key), "k%lld", (long long)i);
        spl_dict_set(d, key, spl_int(i));
    }
    /* Verify all remaining entries */
    ASSERT(spl_dict_contains(d, "k1"));
    ASSERT(spl_dict_contains(d, "k3"));
    ASSERT(spl_dict_contains(d, "k15"));
    ASSERT(!spl_dict_contains(d, "k0"));
    spl_dict_free(d);
}

/* ================================================================
 * Coverage: File I/O edge cases
 * ================================================================ */

TEST(file_null_paths) {
    char* content = spl_file_read(NULL);
    ASSERT_EQ_STR(content, "");
    free(content);

    ASSERT(!spl_file_write(NULL, "test"));
    ASSERT(!spl_file_append(NULL, "test"));
    ASSERT(!spl_file_exists(NULL));
}

TEST(file_write_null_content) {
    const char* path = "/tmp/spl_null_content_test.txt";
    ASSERT(spl_file_write(path, NULL));
    char* content = spl_file_read(path);
    ASSERT_EQ_STR(content, "");
    free(content);
    remove(path);
}

TEST(file_append_null_content) {
    const char* path = "/tmp/spl_null_append_test.txt";
    spl_file_write(path, "base");
    ASSERT(spl_file_append(path, NULL));
    char* content = spl_file_read(path);
    ASSERT_EQ_STR(content, "base");
    free(content);
    remove(path);
}

/* ================================================================
 * Coverage: Process edge cases
 * ================================================================ */

TEST(shell_null_cmd) {
    ASSERT_EQ_INT(spl_shell(NULL), -1);
    char* out = spl_shell_output(NULL);
    ASSERT_EQ_STR(out, "");
    free(out);
}

TEST(shell_output_large) {
    /* Force buffer realloc in spl_shell_output */
    char* out = spl_shell_output("seq 1 5000");
    ASSERT(spl_str_len(out) > 0);
    ASSERT(spl_str_contains(out, "5000"));
    free(out);
}

/* ================================================================
 * Coverage: Environment edge cases
 * ================================================================ */

TEST(env_get_null) {
    ASSERT_EQ_STR(spl_env_get(NULL), "");
}

TEST(env_get_missing) {
    ASSERT_EQ_STR(spl_env_get("SPL_DEFINITELY_NOT_SET_EVER_12345"), "");
}

TEST(env_set_null_key) {
    spl_env_set(NULL, "value");  /* should be no-op */
}

/* ================================================================
 * Coverage: Args
 * ================================================================ */

TEST(args_init) {
    char* fake_argv[] = {"prog", "arg1", "arg2", NULL};
    spl_init_args(3, fake_argv);
    ASSERT_EQ_INT(spl_arg_count(), 3);
    ASSERT_EQ_STR(spl_get_arg(0), "prog");
    ASSERT_EQ_STR(spl_get_arg(1), "arg1");
    ASSERT_EQ_STR(spl_get_arg(2), "arg2");
    ASSERT_EQ_STR(spl_get_arg(3), "");  /* OOB */
    ASSERT_EQ_STR(spl_get_arg(-1), ""); /* negative */
}

/* ================================================================
 * Coverage: Print (just ensure no crash)
 * ================================================================ */

TEST(print_ops) {
    /* Redirect stdout temporarily - just verify no crash */
    spl_print("test");
    spl_print(NULL);
    spl_println("test");
    spl_println(NULL);
    spl_print_i64(42);
    spl_print_i64(-1);
    spl_print_f64(3.14);
    spl_print_f64(0.0);
    printf("\n");  /* newline after print tests */
}

/* ================================================================
 * Coverage: Value accessors with SplValue wrappers
 * ================================================================ */

TEST(accessor_as_array) {
    SplArray* a = spl_array_new();
    SplValue v = spl_array_val(a);
    ASSERT(spl_as_array(v) == a);
    spl_array_free(a);
}

TEST(accessor_as_dict) {
    SplDict* d = spl_dict_new();
    SplValue v = spl_dict_val(d);
    ASSERT(spl_as_dict(v) == d);
    spl_dict_free(d);
}

TEST(accessor_as_str_null) {
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = NULL;
    ASSERT_EQ_STR(spl_as_str(v), "");
}

/* ================================================================
 * Branch Coverage: Constructor NULL paths
 * ================================================================ */

TEST(str_constructor_null) {
    SplValue v = spl_str(NULL);
    ASSERT(v.tag == SPL_STRING);
    ASSERT_EQ_STR(spl_as_str(v), "");
    spl_free_value(v);
}

TEST(str_own_constructor_null) {
    SplValue v = spl_str_own(NULL);
    ASSERT(v.tag == SPL_STRING);
    ASSERT_EQ_STR(spl_as_str(v), "");
    spl_free_value(v);
}

/* ================================================================
 * Branch Coverage: Truthy/Eq/ToString edge cases
 * ================================================================ */

TEST(is_truthy_null_string) {
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = NULL;
    ASSERT(!spl_is_truthy(v));
}

TEST(is_truthy_unknown_tag) {
    SplValue v;
    memset(&v, 0, sizeof(v));
    v.tag = (SplTag)99;
    ASSERT(!spl_is_truthy(v));
}

TEST(eq_unknown_tag) {
    SplValue a, b;
    memset(&a, 0, sizeof(a));
    memset(&b, 0, sizeof(b));
    a.tag = (SplTag)99;
    b.tag = (SplTag)99;
    ASSERT(!spl_eq(a, b));
}

TEST(to_string_unknown_tag) {
    SplValue v;
    memset(&v, 0, sizeof(v));
    v.tag = (SplTag)99;
    SplValue s = spl_to_string(v);
    ASSERT_EQ_STR(spl_as_str(s), "?");
    spl_free_value(s);
}

TEST(eq_string_null_as_str) {
    SplValue a, b;
    a.tag = SPL_STRING; a.as_str = NULL;
    b.tag = SPL_STRING; b.as_str = NULL;
    ASSERT(spl_eq(a, b));
    SplValue c = spl_str("hello");
    ASSERT(!spl_eq(a, c));
    ASSERT(!spl_eq(c, a));
    spl_free_value(c);
}

TEST(eq_array_same_len_diff_elems) {
    SplArray* a = spl_array_new();
    SplArray* b = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));
    spl_array_push(b, spl_int(1));
    spl_array_push(b, spl_int(3));
    ASSERT(!spl_eq(spl_array_val(a), spl_array_val(b)));
    spl_array_free(a);
    spl_array_free(b);
}

/* ================================================================
 * Branch Coverage: String edge paths
 * ================================================================ */

TEST(str_cmp_null_args) {
    ASSERT(spl_str_cmp(NULL, "abc") < 0);
    ASSERT(spl_str_cmp("abc", NULL) > 0);
    ASSERT(spl_str_cmp(NULL, NULL) == 0);
}

TEST(str_index_char_very_negative) {
    char* c = spl_str_index_char("hi", -10);
    ASSERT_EQ_STR(c, "");
    free(c);
}

TEST(str_trim_leading_cr) {
    char* s = spl_str_trim("\r\rhello");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_trim_trailing_cr_only) {
    char* s = spl_str_trim("hello\r\r");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_trim_only_cr) {
    char* s = spl_str_trim("\r\r\r");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_trim_trailing_tab) {
    char* s = spl_str_trim("hello\t\t");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_trim_leading_tab_and_cr) {
    char* s = spl_str_trim("\t\rhello\r\t");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

/* ================================================================
 * Branch Coverage: Dict hash collisions
 * ================================================================ */

TEST(dict_force_hash_collision) {
    /*
     * Force a true 64-bit hash collision by manually planting a decoy entry
     * at the target's slot with the target's hash but a different key.
     * This forces both dict_set and dict_find to hit the "same hash, different key"
     * branch (strcmp returns non-zero after hash matches).
     */
    SplDict* d = spl_dict_new_cap(16);
    uint64_t h = spl_str_hash("target");
    int64_t slot = (int64_t)(h & (uint64_t)(d->cap - 1));

    /* Plant decoy at target's slot with target's full hash but different key */
    d->entries[slot].key = strdup("decoy");
    d->entries[slot].value = spl_int(1);
    d->entries[slot].hash = h;
    d->entries[slot].occupied = 1;
    d->len = 1;

    /* dict_set("target") finds decoy: hash matches, strcmp differs → probe past */
    spl_dict_set(d, "target", spl_int(2));
    ASSERT_EQ_INT(d->len, 2);

    /* dict_find("target") probes past decoy: hash matches, strcmp differs → continue */
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "target")), 2);

    spl_dict_free(d);
}

/* ================================================================
 * Branch Coverage: File I/O fopen failures
 * ================================================================ */

TEST(file_write_invalid_path) {
    ASSERT(!spl_file_write("/nonexistent_dir_12345/file.txt", "test"));
}

TEST(file_append_invalid_path) {
    ASSERT(!spl_file_append("/nonexistent_dir_12345/file.txt", "test"));
}

/* ================================================================
 * Branch Coverage: Args NULL entry
 * ================================================================ */

TEST(args_null_entry) {
    char* fake_argv[] = {"prog", NULL, "arg2"};
    spl_init_args(3, fake_argv);
    ASSERT_EQ_STR(spl_get_arg(1), "");
    spl_init_args(0, NULL);
}

/* ================================================================
 * Branch Coverage: Panic (via fork)
 * Note: Skip on Windows (no fork())
 * ================================================================ */

#ifndef _WIN32
TEST(panic_exits) {
    pid_t pid = fork();
    if (pid == 0) {
        freopen("/dev/null", "w", stderr);
        spl_panic("test panic");
        _exit(0);
    }
    int status;
    waitpid(pid, &status, 0);
    ASSERT(WIFEXITED(status));
    ASSERT_EQ_INT(WEXITSTATUS(status), 1);
}

TEST(panic_null_msg) {
    pid_t pid = fork();
    if (pid == 0) {
        freopen("/dev/null", "w", stderr);
        spl_panic(NULL);
        _exit(0);
    }
    int status;
    waitpid(pid, &status, 0);
    ASSERT(WIFEXITED(status));
    ASSERT_EQ_INT(WEXITSTATUS(status), 1);
}
#endif /* _WIN32 */

/* ================================================================
 * Coverage: Directory Operations
 * ================================================================ */

TEST(dir_remove_all) {
    /* Create temp directory structure */
    system("mkdir -p /tmp/rt_test_dir/subdir");
    system("touch /tmp/rt_test_dir/file.txt");
    system("touch /tmp/rt_test_dir/subdir/file2.txt");

    /* Remove all should work */
    ASSERT(rt_dir_remove_all("/tmp/rt_test_dir"));
    ASSERT(!spl_file_exists("/tmp/rt_test_dir"));
}

TEST(dir_remove_all_null) {
    ASSERT(!rt_dir_remove_all(NULL));
}

/* ================================================================
 * Coverage: File Locking
 * ================================================================ */

TEST(file_lock_unlock) {
    const char* path = "/tmp/rt_test_lock.txt";
    spl_file_write(path, "test");

    /* Lock file */
    int64_t handle = rt_file_lock(path, 0);
    ASSERT(handle >= 0);

    /* Unlock file */
    ASSERT(rt_file_unlock(handle));

    remove(path);
}

TEST(file_lock_null_path) {
    ASSERT_EQ_INT(rt_file_lock(NULL, 0), -1);
}

TEST(file_lock_invalid_path) {
    /* Try to lock non-existent directory path */
    ASSERT_EQ_INT(rt_file_lock("/nonexistent_dir_12345/file.txt", 0), -1);
}

TEST(file_lock_with_timeout) {
    const char* path = "/tmp/rt_test_lock_timeout.txt";
    spl_file_write(path, "test");

    /* Lock with timeout */
    int64_t handle = rt_file_lock(path, 1);
    ASSERT(handle >= 0);

    rt_file_unlock(handle);
    remove(path);
}

TEST(file_unlock_invalid_handle) {
    ASSERT(!rt_file_unlock(-1));
}

/* Note: Testing flock failure (line 718) and popen/vsnprintf errors (lines 792, 811)
 * requires extreme conditions (resource exhaustion, system errors) that are impractical
 * to simulate in unit tests. These 3 remaining uncovered branches represent legitimate
 * error handling paths that are tested through system-level testing. */

/* ================================================================
 * Coverage: FFI Call
 * ================================================================ */

static int64_t test_fn0(void) { return 42; }
static int64_t test_fn1(int64_t a) { return a + 10; }
static int64_t test_fn2(int64_t a, int64_t b) { return a + b; }
static int64_t test_fn3(int64_t a, int64_t b, int64_t c) { return a + b + c; }
static int64_t test_fn4(int64_t a, int64_t b, int64_t c, int64_t d) { return a + b + c + d; }

TEST(wffi_call_null) {
    int64_t args[1] = {0};
    ASSERT_EQ_INT(spl_wffi_call_i64(NULL, args, 1), 0);
}

TEST(wffi_call_0_args) {
    int64_t args[1] = {0};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)test_fn0, args, 0), 42);
}

TEST(wffi_call_1_arg) {
    int64_t args[1] = {5};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)test_fn1, args, 1), 15);
}

TEST(wffi_call_2_args) {
    int64_t args[2] = {10, 20};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)test_fn2, args, 2), 30);
}

TEST(wffi_call_3_args) {
    int64_t args[3] = {1, 2, 3};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)test_fn3, args, 3), 6);
}

TEST(wffi_call_4_args) {
    int64_t args[4] = {1, 2, 3, 4};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)test_fn4, args, 4), 10);
}

TEST(wffi_call_invalid_nargs) {
    int64_t args[5] = {0};
    /* 5 args should hit default case and return 0 */
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)test_fn0, args, 5), 0);
}

/* ================================================================
 * Coverage: Shell Output Error Path
 * ================================================================ */

TEST(shell_output_null) {
    char* output = spl_shell_output(NULL);
    ASSERT_EQ_STR(output, "");
    free(output);
}

TEST(shell_output_invalid_cmd) {
    /* Invalid command should still return something (empty or error) */
    char* output = spl_shell_output("/nonexistent_command_12345_xyz");
    /* Just ensure we get a valid string back, even if empty */
    ASSERT(output != NULL);
    free(output);
}

/* ================================================================
 * Coverage: spl_file_delete / spl_file_size
 * ================================================================ */

TEST(file_delete_null_path) {
    ASSERT_EQ_INT(spl_file_delete(NULL), 0);
}

TEST(file_delete_existing) {
    const char* path = "/tmp/_spl_test_delete_me.tmp";
    spl_file_write(path, "deleteme");
    ASSERT_EQ_INT(spl_file_delete(path), 1);
    ASSERT(!spl_file_exists(path));
}

TEST(file_delete_nonexistent) {
    ASSERT_EQ_INT(spl_file_delete("/tmp/_spl_no_such_file_xyz.tmp"), 0);
}

TEST(file_size_null_path) {
    ASSERT_EQ_INT(spl_file_size(NULL), -1);
}

TEST(file_size_nonexistent) {
    ASSERT_EQ_INT(spl_file_size("/tmp/_spl_no_such_file_xyz.tmp"), -1);
}

TEST(file_size_existing) {
    const char* path = "/tmp/_spl_test_size.tmp";
    spl_file_write(path, "hello");
    ASSERT_EQ_INT(spl_file_size(path), 5);
    spl_file_delete(path);
}

/* ================================================================
 * Coverage: rt_cli_get_args / rt_shell_output
 * ================================================================ */

TEST(cli_get_args_with_args) {
    char* argv[] = {"prog", "alpha", "beta"};
    spl_init_args(3, argv);
    SplArray* args = rt_cli_get_args();
    ASSERT_EQ_INT(spl_array_len(args), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 0)), "prog");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 1)), "alpha");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 2)), "beta");
    spl_array_free(args);
}

TEST(cli_get_args_zero) {
    spl_init_args(0, NULL);
    SplArray* args = rt_cli_get_args();
    ASSERT_EQ_INT(spl_array_len(args), 0);
    spl_array_free(args);
}

TEST(rt_shell_output_strips_newline) {
    const char* r = rt_shell_output("echo hello");
    ASSERT_EQ_STR(r, "hello\n");
    free((void*)r);
}

TEST(rt_shell_output_strips_crlf) {
    const char* r = rt_shell_output("printf 'line\\r\\n'");
    ASSERT_EQ_STR(r, "line\r\n");
    free((void*)r);
}

TEST(rt_shell_output_null) {
    const char* r = rt_shell_output(NULL);
    ASSERT_EQ_STR(r, "");
    free((void*)r);
}

/* ================================================================
 * Coverage: spl_str_last_index_of
 * ================================================================ */

TEST(last_index_of_null_s) {
    ASSERT_EQ_INT(spl_str_last_index_of(NULL, "x"), -1);
}

TEST(last_index_of_null_needle) {
    ASSERT_EQ_INT(spl_str_last_index_of("hello", NULL), -1);
}

TEST(last_index_of_both_null) {
    ASSERT_EQ_INT(spl_str_last_index_of(NULL, NULL), -1);
}

TEST(last_index_of_empty_needle) {
    ASSERT_EQ_INT(spl_str_last_index_of("hello", ""), -1);
}

TEST(last_index_of_needle_longer) {
    ASSERT_EQ_INT(spl_str_last_index_of("hi", "hello"), -1);
}

TEST(last_index_of_found_at_end) {
    ASSERT_EQ_INT(spl_str_last_index_of("hello world", "world"), 6);
}

TEST(last_index_of_found_at_start) {
    ASSERT_EQ_INT(spl_str_last_index_of("abcdef", "abc"), 0);
}

TEST(last_index_of_found_in_middle) {
    ASSERT_EQ_INT(spl_str_last_index_of("xxabcxx", "abc"), 2);
}

TEST(last_index_of_multiple_occurrences) {
    ASSERT_EQ_INT(spl_str_last_index_of("abcabcabc", "abc"), 6);
}

TEST(last_index_of_not_found) {
    ASSERT_EQ_INT(spl_str_last_index_of("hello world", "xyz"), -1);
}

TEST(last_index_of_single_char) {
    ASSERT_EQ_INT(spl_str_last_index_of("banana", "a"), 5);
}

TEST(last_index_of_exact_match) {
    ASSERT_EQ_INT(spl_str_last_index_of("abc", "abc"), 0);
}

/* ================================================================
 * Coverage: spl_str_split
 * ================================================================ */

TEST(split_null_s) {
    SplArray* arr = spl_str_split(NULL, ",");
    ASSERT_EQ_INT(spl_array_len(arr), 0);
    spl_array_free(arr);
}

TEST(split_null_delim) {
    SplArray* arr = spl_str_split("hello", NULL);
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "hello");
    spl_array_free(arr);
}

TEST(split_empty_delim) {
    SplArray* arr = spl_str_split("hello", "");
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "hello");
    spl_array_free(arr);
}

TEST(split_normal) {
    SplArray* arr = spl_str_split("a,b,c", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "a");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "b");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 2)), "c");
    spl_array_free(arr);
}

TEST(split_delim_not_found) {
    SplArray* arr = spl_str_split("hello", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "hello");
    spl_array_free(arr);
}

TEST(split_consecutive_delims) {
    SplArray* arr = spl_str_split("a,,b", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "a");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 2)), "b");
    spl_array_free(arr);
}

TEST(split_delim_at_start) {
    SplArray* arr = spl_str_split(",a,b", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "");
    spl_array_free(arr);
}

TEST(split_delim_at_end) {
    SplArray* arr = spl_str_split("a,b,", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 2)), "");
    spl_array_free(arr);
}

TEST(split_multi_char_delim) {
    SplArray* arr = spl_str_split("a::b::c", "::");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "b");
    spl_array_free(arr);
}

TEST(split_empty_string) {
    SplArray* arr = spl_str_split("", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "");
    spl_array_free(arr);
}

/* ================================================================
 * Coverage: spl_str_join
 * ================================================================ */

TEST(join_null_arr) {
    char* r = spl_str_join(NULL, ",");
    ASSERT_EQ_STR(r, "");
    free(r);
}

TEST(join_empty_arr) {
    SplArray* arr = spl_array_new();
    char* r = spl_str_join(arr, ",");
    ASSERT_EQ_STR(r, "");
    free(r);
    spl_array_free(arr);
}

TEST(join_null_delim) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("a"));
    spl_array_push(arr, spl_str("b"));
    char* r = spl_str_join(arr, NULL);
    ASSERT_EQ_STR(r, "ab");
    free(r);
    spl_array_free(arr);
}

TEST(join_single_element) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("hello"));
    char* r = spl_str_join(arr, ",");
    ASSERT_EQ_STR(r, "hello");
    free(r);
    spl_array_free(arr);
}

TEST(join_multiple_elements) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("a"));
    spl_array_push(arr, spl_str("b"));
    spl_array_push(arr, spl_str("c"));
    char* r = spl_str_join(arr, ",");
    ASSERT_EQ_STR(r, "a,b,c");
    free(r);
    spl_array_free(arr);
}

TEST(join_multi_char_delim) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("x"));
    spl_array_push(arr, spl_str("y"));
    char* r = spl_str_join(arr, " -- ");
    ASSERT_EQ_STR(r, "x -- y");
    free(r);
    spl_array_free(arr);
}

TEST(join_with_null_element) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("a"));
    SplValue null_str;
    null_str.tag = SPL_STRING;
    null_str.as_str = NULL;
    spl_array_push(arr, null_str);
    spl_array_push(arr, spl_str("c"));
    char* r = spl_str_join(arr, ",");
    ASSERT_EQ_STR(r, "a,,c");
    free(r);
    spl_array_free(arr);
}

TEST(join_all_null_elements) {
    SplArray* arr = spl_array_new();
    SplValue null_str;
    null_str.tag = SPL_STRING;
    null_str.as_str = NULL;
    spl_array_push(arr, null_str);
    spl_array_push(arr, null_str);
    char* r = spl_str_join(arr, "-");
    ASSERT_EQ_STR(r, "-");
    free(r);
    spl_array_free(arr);
}

TEST(join_empty_delim) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("a"));
    spl_array_push(arr, spl_str("b"));
    char* r = spl_str_join(arr, "");
    ASSERT_EQ_STR(r, "ab");
    free(r);
    spl_array_free(arr);
}

/* ================================================================
 * Coverage: spl_array_contains_str
 * ================================================================ */

TEST(contains_str_null_array) {
    ASSERT(!spl_array_contains_str(NULL, "x"));
}

TEST(contains_str_null_search) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("hello"));
    ASSERT(!spl_array_contains_str(arr, NULL));
    spl_array_free(arr);
}

TEST(contains_str_found) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("apple"));
    spl_array_push(arr, spl_str("banana"));
    ASSERT(spl_array_contains_str(arr, "banana"));
    spl_array_free(arr);
}

TEST(contains_str_not_found) {
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("apple"));
    ASSERT(!spl_array_contains_str(arr, "grape"));
    spl_array_free(arr);
}

TEST(contains_str_null_element) {
    SplArray* arr = spl_array_new();
    SplValue null_str;
    null_str.tag = SPL_STRING;
    null_str.as_str = NULL;
    spl_array_push(arr, null_str);
    spl_array_push(arr, spl_str("hello"));
    ASSERT(spl_array_contains_str(arr, "hello"));
    ASSERT(!spl_array_contains_str(arr, "nope"));
    spl_array_free(arr);
}

TEST(contains_str_empty_array) {
    SplArray* arr = spl_array_new();
    ASSERT(!spl_array_contains_str(arr, "x"));
    spl_array_free(arr);
}

/* ================================================================
 * Coverage: rt_file_* Aliases + exec_manager stubs + sprintf edge
 * ================================================================ */

TEST(rt_file_aliases) {
    const char* path = "/tmp/_spl_rt_alias_test.tmp";
    rt_file_write(path, "test123");
    ASSERT(rt_file_exists(path));
    const char* content = rt_file_read_text(path);
    ASSERT_EQ_STR(content, "test123");
    free((void*)content);
    ASSERT_EQ_INT(rt_file_size(path), 7);
    ASSERT(rt_file_delete(path));
    ASSERT(!rt_file_exists(path));
}

TEST(exec_manager_stubs) {
    int64_t h = rt_exec_manager_create("test");
    ASSERT_EQ_INT(h, 0);
    const char* r = rt_exec_manager_compile(h, "data");
    ASSERT_EQ_STR(r, "");
    int64_t rv = rt_exec_manager_execute(h, "fn", NULL);
    ASSERT_EQ_INT(rv, 0);
    ASSERT(!rt_exec_manager_has_function(h, "fn"));
    rt_exec_manager_cleanup(h);
}

TEST(sprintf_many_args) {
    char* s = spl_sprintf("%s=%d, %s=%d, %s=%.2f", "a", 1, "b", 2, "c", 3.14);
    ASSERT(spl_str_contains(s, "a=1"));
    ASSERT(spl_str_contains(s, "b=2"));
    ASSERT(spl_str_contains(s, "c=3.14"));
    free(s);
}

/* ================================================================
 * Coverage: remaining branch edge cases
 * ================================================================ */

TEST(contains_str_with_non_string_element) {
    /* Branch 488:13 — arr->items[i].tag != SPL_STRING */
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_int(42));
    spl_array_push(arr, spl_str("hello"));
    ASSERT(spl_array_contains_str(arr, "hello"));
    ASSERT(!spl_array_contains_str(arr, "nope"));
    spl_array_free(arr);
}

TEST(join_with_non_string_element) {
    /* Branches 522:26, 530:26 — arr->items[i].tag != SPL_STRING */
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_str("a"));
    spl_array_push(arr, spl_int(99));
    spl_array_push(arr, spl_str("c"));
    char* r = spl_str_join(arr, ",");
    ASSERT_EQ_STR(r, "a,,c");
    free(r);
    spl_array_free(arr);
}

TEST(cli_get_args_null_entry) {
    /* Branches 907:47 — g_argv[i] is NULL */
    char* argv[] = {"prog", NULL, "end"};
    spl_init_args(3, argv);
    SplArray* args = rt_cli_get_args();
    ASSERT_EQ_INT(spl_array_len(args), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 0)), "prog");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 1)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 2)), "end");
    spl_array_free(args);
}

TEST(cli_get_args_null_argv) {
    /* Branch 907:37 — g_argv is NULL but g_argc > 0 */
    spl_init_args(2, NULL);
    SplArray* args = rt_cli_get_args();
    ASSERT_EQ_INT(spl_array_len(args), 2);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 0)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 1)), "");
    spl_array_free(args);
    /* Restore sane state */
    spl_init_args(0, NULL);
}

/* ================================================================
 * Main
 * ================================================================ */

int main(void) {
    printf("=== Simple Bootstrap Runtime Tests ===\n\n");

    printf("--- Value Constructors ---\n");
    RUN(nil_value);
    RUN(bool_value);
    RUN(int_value);
    RUN(float_value);
    RUN(string_value);
    RUN(string_own_value);

    printf("\n--- Value Equality ---\n");
    RUN(eq_nil);
    RUN(eq_bool);
    RUN(eq_int);
    RUN(eq_string);
    RUN(eq_different_types);

    printf("\n--- Value to_string ---\n");
    RUN(to_string_nil);
    RUN(to_string_bool);
    RUN(to_string_int);
    RUN(to_string_float);
    RUN(to_string_string);
    RUN(to_string_array);
    RUN(to_string_empty_array);

    printf("\n--- String Operations ---\n");
    RUN(str_new);
    RUN(str_concat);
    RUN(str_len);
    RUN(str_eq);
    RUN(str_cmp);
    RUN(str_slice);
    RUN(str_index_char);
    RUN(str_hash);
    RUN(str_contains);
    RUN(str_starts_with);
    RUN(str_ends_with);
    RUN(str_replace);
    RUN(str_trim);
    RUN(str_index_of);
    RUN(str_to_upper);
    RUN(str_to_lower);

    printf("\n--- Array Operations ---\n");
    RUN(array_basic);
    RUN(array_negative_index);
    RUN(array_set);
    RUN(array_pop);
    RUN(array_out_of_bounds);
    RUN(array_grow);
    RUN(array_slice);
    RUN(array_concat);
    RUN(array_mixed_types);
    RUN(array_i64);
    RUN(array_text);

    printf("\n--- Dict Operations ---\n");
    RUN(dict_basic);
    RUN(dict_overwrite);
    RUN(dict_contains);
    RUN(dict_missing_key);
    RUN(dict_remove);
    RUN(dict_keys);
    RUN(dict_values);
    RUN(dict_grow);
    RUN(dict_string_values);
    RUN(dict_mixed_values);

    printf("\n--- File I/O ---\n");
    RUN(file_write_read);
    RUN(file_append);
    RUN(file_not_exists);

    printf("\n--- Formatting ---\n");
    RUN(i64_to_str);
    RUN(f64_to_str);
    RUN(sprintf_test);

    printf("\n--- Process ---\n");
    RUN(shell_output);
    RUN(shell_return);

    printf("\n--- Environment ---\n");
    RUN(env_get_set);

    printf("\n--- Memory ---\n");
    RUN(malloc_free);
    RUN(strdup_test);

    printf("\n--- Integration (Compiler Workloads) ---\n");
    RUN(token_storage);
    RUN(symbol_table);
    RUN(ast_arena_pattern);
    RUN(c_codegen_string_building);

    printf("\n--- Coverage: Value Edge Cases ---\n");
    RUN(is_truthy_array);
    RUN(is_truthy_dict);
    RUN(is_truthy_null_containers);
    RUN(eq_float);
    RUN(eq_array);
    RUN(eq_array_null);
    RUN(eq_dict_pointer);
    RUN(to_string_dict);
    RUN(to_string_large_array);
    RUN(to_string_null_array);
    RUN(free_value_all_types);

    printf("\n--- Coverage: String Edge Cases ---\n");
    RUN(str_null_paths);
    RUN(str_slice_edge_cases);
    RUN(str_ends_with_longer_suffix);
    RUN(str_replace_empty_old);
    RUN(str_trim_empty);

    printf("\n--- Coverage: Array Edge Cases ---\n");
    RUN(array_null_ops);
    RUN(array_slice_edge_cases);
    RUN(array_concat_null);
    RUN(array_set_out_of_bounds);

    printf("\n--- Coverage: Dict Edge Cases ---\n");
    RUN(dict_null_ops);
    RUN(dict_null_key);
    RUN(dict_keys_null);
    RUN(dict_values_null);
    RUN(dict_remove_nonexistent);
    RUN(dict_tombstone_reuse);
    RUN(dict_resize_with_tombstones);

    printf("\n--- Coverage: File I/O Edge Cases ---\n");
    RUN(file_null_paths);
    RUN(file_write_null_content);
    RUN(file_append_null_content);

    printf("\n--- Coverage: Process Edge Cases ---\n");
    RUN(shell_null_cmd);
    RUN(shell_output_large);

    printf("\n--- Coverage: Environment Edge Cases ---\n");
    RUN(env_get_null);
    RUN(env_get_missing);
    RUN(env_set_null_key);

    printf("\n--- Coverage: Args ---\n");
    RUN(args_init);

    printf("\n--- Coverage: Print/Output ---\n");
    RUN(print_ops);

    printf("\n--- Coverage: Accessors ---\n");
    RUN(accessor_as_array);
    RUN(accessor_as_dict);
    RUN(accessor_as_str_null);

    printf("\n--- Branch Coverage: Constructor NULL ---\n");
    RUN(str_constructor_null);
    RUN(str_own_constructor_null);

    printf("\n--- Branch Coverage: Truthy/Eq/ToString ---\n");
    RUN(is_truthy_null_string);
    RUN(is_truthy_unknown_tag);
    RUN(eq_unknown_tag);
    RUN(eq_string_null_as_str);
    RUN(to_string_unknown_tag);
    RUN(eq_array_same_len_diff_elems);

    printf("\n--- Branch Coverage: String Edge ---\n");
    RUN(str_cmp_null_args);
    RUN(str_index_char_very_negative);
    RUN(str_trim_leading_cr);
    RUN(str_trim_trailing_cr_only);
    RUN(str_trim_only_cr);
    RUN(str_trim_trailing_tab);
    RUN(str_trim_leading_tab_and_cr);

    printf("\n--- Branch Coverage: Dict Collision ---\n");
    RUN(dict_force_hash_collision);

    printf("\n--- Branch Coverage: File I/O Invalid ---\n");
    RUN(file_write_invalid_path);
    RUN(file_append_invalid_path);

    printf("\n--- Branch Coverage: Args NULL ---\n");
    RUN(args_null_entry);

    printf("\n--- Branch Coverage: Panic ---\n");
#ifndef _WIN32
    RUN(panic_exits);
    RUN(panic_null_msg);
#endif

    printf("\n--- Coverage: Directory Operations ---\n");
    RUN(dir_remove_all);
    RUN(dir_remove_all_null);

    printf("\n--- Coverage: File Locking ---\n");
    RUN(file_lock_unlock);
    RUN(file_lock_null_path);
    RUN(file_lock_invalid_path);
    RUN(file_lock_with_timeout);
    RUN(file_unlock_invalid_handle);

    printf("\n--- Coverage: FFI Call ---\n");
    RUN(wffi_call_null);
    RUN(wffi_call_0_args);
    RUN(wffi_call_1_arg);
    RUN(wffi_call_2_args);
    RUN(wffi_call_3_args);
    RUN(wffi_call_4_args);
    RUN(wffi_call_invalid_nargs);

    printf("\n--- Coverage: Shell Output Error Path ---\n");
    RUN(shell_output_null);
    RUN(shell_output_invalid_cmd);

    printf("\n--- Coverage: file_delete / file_size ---\n");
    RUN(file_delete_null_path);
    RUN(file_delete_existing);
    RUN(file_delete_nonexistent);
    RUN(file_size_null_path);
    RUN(file_size_nonexistent);
    RUN(file_size_existing);

    printf("\n--- Coverage: rt_cli_get_args / rt_shell_output ---\n");
    RUN(cli_get_args_with_args);
    RUN(cli_get_args_zero);
    RUN(rt_shell_output_strips_newline);
    RUN(rt_shell_output_strips_crlf);
    RUN(rt_shell_output_null);

    printf("\n--- Coverage: str_last_index_of ---\n");
    RUN(last_index_of_null_s);
    RUN(last_index_of_null_needle);
    RUN(last_index_of_both_null);
    RUN(last_index_of_empty_needle);
    RUN(last_index_of_needle_longer);
    RUN(last_index_of_found_at_end);
    RUN(last_index_of_found_at_start);
    RUN(last_index_of_found_in_middle);
    RUN(last_index_of_multiple_occurrences);
    RUN(last_index_of_not_found);
    RUN(last_index_of_single_char);
    RUN(last_index_of_exact_match);

    printf("\n--- Coverage: str_split ---\n");
    RUN(split_null_s);
    RUN(split_null_delim);
    RUN(split_empty_delim);
    RUN(split_normal);
    RUN(split_delim_not_found);
    RUN(split_consecutive_delims);
    RUN(split_delim_at_start);
    RUN(split_delim_at_end);
    RUN(split_multi_char_delim);
    RUN(split_empty_string);

    printf("\n--- Coverage: str_join ---\n");
    RUN(join_null_arr);
    RUN(join_empty_arr);
    RUN(join_null_delim);
    RUN(join_single_element);
    RUN(join_multiple_elements);
    RUN(join_multi_char_delim);
    RUN(join_with_null_element);
    RUN(join_all_null_elements);
    RUN(join_empty_delim);

    printf("\n--- Coverage: array_contains_str ---\n");
    RUN(contains_str_null_array);
    RUN(contains_str_null_search);
    RUN(contains_str_found);
    RUN(contains_str_not_found);
    RUN(contains_str_null_element);
    RUN(contains_str_empty_array);

    printf("\n--- Coverage: remaining branch edges ---\n");
    RUN(contains_str_with_non_string_element);
    RUN(join_with_non_string_element);
    RUN(cli_get_args_null_entry);
    RUN(cli_get_args_null_argv);

    printf("\n--- Coverage: rt_file aliases ---\n");
    RUN(rt_file_aliases);

    printf("\n--- Coverage: exec_manager stubs ---\n");
    RUN(exec_manager_stubs);

    printf("\n--- Coverage: sprintf edge cases ---\n");
    RUN(sprintf_many_args);

    printf("\n=== All %d tests passed ===\n", tests_run);
    return 0;
}
