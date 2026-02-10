/*
 * Simple Bootstrap Runtime — Test Suite
 *
 * Build and run:
 *   gcc -o /tmp/runtime_test bootstrap/runtime_test.c bootstrap/runtime.c -std=c11 && /tmp/runtime_test
 */

#define _POSIX_C_SOURCE 200809L

#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) static void test_##name(void)
#define RUN(name) do { \
    printf("  %-50s", #name); \
    test_##name(); \
    tests_passed++; \
    printf(" PASS\n"); \
} while(0)

#define ASSERT(cond) do { \
    if (!(cond)) { \
        printf(" FAIL\n    Assertion failed: %s\n    at %s:%d\n", #cond, __FILE__, __LINE__); \
        tests_failed++; \
        return; \
    } \
} while(0)

#define ASSERT_EQ_INT(a, b) do { \
    int64_t _a = (a), _b = (b); \
    if (_a != _b) { \
        printf(" FAIL\n    Expected %lld == %lld\n    at %s:%d\n", \
               (long long)_a, (long long)_b, __FILE__, __LINE__); \
        tests_failed++; \
        return; \
    } \
} while(0)

#define ASSERT_EQ_STR(a, b) do { \
    const char* _a = (a); const char* _b = (b); \
    if (strcmp(_a ? _a : "", _b ? _b : "") != 0) { \
        printf(" FAIL\n    Expected \"%s\" == \"%s\"\n    at %s:%d\n", \
               _a ? _a : "(null)", _b ? _b : "(null)", __FILE__, __LINE__); \
        tests_failed++; \
        return; \
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

    printf("\n=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);

    return tests_failed > 0 ? 1 : 0;
}
