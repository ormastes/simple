/*
 * Simple Bootstrap Runtime — Branch Coverage Test Suite
 *
 * Targets UNCOVERED BRANCHES in runtime.c that runtime_test.c does not reach.
 * Each test function is small and targets one specific branch or edge case.
 *
 * Build (Windows/MinGW clang):
 *   clang -o runtime_branch_test.exe runtime_branch_test.c runtime.c -std=c11
 *
 * Build (Linux/macOS):
 *   cc -o runtime_branch_test runtime_branch_test.c runtime.c -std=c11 -ldl
 */

#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include <io.h>
#include <process.h>
#else
#include <sys/wait.h>
#include <unistd.h>
#endif

static int tests_run = 0;
static int tests_passed = 0;

#define TEST(name) static void test_##name(void)
#define RUN(name) do { \
    tests_run++; \
    printf("  %-60s", #name); \
    fflush(stdout); \
    test_##name(); \
    tests_passed++; \
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

#define ASSERT_NOT_NULL(p) do { \
    if ((p) == NULL) { \
        printf(" FAIL\n    expected non-NULL\n    %s:%d\n", __FILE__, __LINE__); \
        exit(1); \
    } \
} while(0)

/* Helper to get a temp file path that works on Windows and Unix */
#ifdef _WIN32
#define TMP_DIR "."
#define TMP_PREFIX ".\\__btest_"
#else
#define TMP_DIR "/tmp"
#define TMP_PREFIX "/tmp/__btest_"
#endif

/* ================================================================
 * 1. spl_is_truthy — Branch Coverage
 * ================================================================ */

TEST(truthy_array_null_ptr) {
    /* SPL_ARRAY with NULL array ptr => falsy */
    SplValue v;
    v.tag = SPL_ARRAY;
    v.as_array = NULL;
    ASSERT(!spl_is_truthy(v));
}

TEST(truthy_array_empty) {
    /* SPL_ARRAY with empty array => falsy */
    SplArray* a = spl_array_new();
    ASSERT(!spl_is_truthy(spl_array_val(a)));
    spl_array_free(a);
}

TEST(truthy_array_nonempty) {
    /* SPL_ARRAY with elements => truthy */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(42));
    ASSERT(spl_is_truthy(spl_array_val(a)));
    spl_array_free(a);
}

TEST(truthy_dict_null_ptr) {
    /* SPL_DICT with NULL dict ptr => falsy */
    SplValue v;
    v.tag = SPL_DICT;
    v.as_dict = NULL;
    ASSERT(!spl_is_truthy(v));
}

TEST(truthy_dict_empty) {
    /* SPL_DICT with len==0 => falsy */
    SplDict* d = spl_dict_new();
    ASSERT(!spl_is_truthy(spl_dict_val(d)));
    spl_dict_free(d);
}

TEST(truthy_dict_nonempty) {
    /* SPL_DICT with entries => truthy */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "k", spl_int(1));
    ASSERT(spl_is_truthy(spl_dict_val(d)));
    spl_dict_free(d);
}

TEST(truthy_string_null_ptr) {
    /* SPL_STRING with NULL as_str => falsy */
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = NULL;
    ASSERT(!spl_is_truthy(v));
}

TEST(truthy_string_empty) {
    /* SPL_STRING with empty string => falsy */
    SplValue v = spl_str("");
    ASSERT(!spl_is_truthy(v));
    spl_free_value(v);
}

TEST(truthy_string_nonempty) {
    /* SPL_STRING with content => truthy */
    SplValue v = spl_str("hello");
    ASSERT(spl_is_truthy(v));
    spl_free_value(v);
}

TEST(truthy_default_unknown_tag) {
    /* Unknown tag falls through switch, hits return 0 */
    SplValue v;
    memset(&v, 0, sizeof(v));
    v.tag = (SplTag)99;
    ASSERT(!spl_is_truthy(v));
}

/* ================================================================
 * 2. spl_eq — Branch Coverage
 * ================================================================ */

TEST(eq_array_both_null) {
    /* Both array ptrs NULL => equal */
    SplValue a, b;
    a.tag = SPL_ARRAY; a.as_array = NULL;
    b.tag = SPL_ARRAY; b.as_array = NULL;
    ASSERT(spl_eq(a, b));
}

TEST(eq_array_one_null_left) {
    /* Left NULL, right not => not equal */
    SplValue a;
    a.tag = SPL_ARRAY; a.as_array = NULL;
    SplArray* arr = spl_array_new();
    SplValue b = spl_array_val(arr);
    ASSERT(!spl_eq(a, b));
    spl_array_free(arr);
}

TEST(eq_array_one_null_right) {
    /* Left not NULL, right NULL => not equal */
    SplArray* arr = spl_array_new();
    SplValue a = spl_array_val(arr);
    SplValue b;
    b.tag = SPL_ARRAY; b.as_array = NULL;
    ASSERT(!spl_eq(a, b));
    spl_array_free(arr);
}

TEST(eq_array_same_pointer) {
    /* Same pointer, same len => equal (element-wise check) */
    SplArray* arr = spl_array_new();
    spl_array_push(arr, spl_int(1));
    spl_array_push(arr, spl_int(2));
    ASSERT(spl_eq(spl_array_val(arr), spl_array_val(arr)));
    spl_array_free(arr);
}

TEST(eq_array_matching_elements) {
    /* Two arrays with same elements => equal */
    SplArray* a = spl_array_new();
    SplArray* b = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_push(a, spl_int(20));
    spl_array_push(a, spl_int(30));
    spl_array_push(b, spl_int(10));
    spl_array_push(b, spl_int(20));
    spl_array_push(b, spl_int(30));
    ASSERT(spl_eq(spl_array_val(a), spl_array_val(b)));
    spl_array_free(a);
    spl_array_free(b);
}

TEST(eq_array_diff_length) {
    /* Different lengths => not equal */
    SplArray* a = spl_array_new();
    SplArray* b = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(b, spl_int(1));
    spl_array_push(b, spl_int(2));
    ASSERT(!spl_eq(spl_array_val(a), spl_array_val(b)));
    spl_array_free(a);
    spl_array_free(b);
}

TEST(eq_array_same_len_diff_elem) {
    /* Same length, differing element => not equal (early exit from loop) */
    SplArray* a = spl_array_new();
    SplArray* b = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));
    spl_array_push(a, spl_int(3));
    spl_array_push(b, spl_int(1));
    spl_array_push(b, spl_int(999));
    spl_array_push(b, spl_int(3));
    ASSERT(!spl_eq(spl_array_val(a), spl_array_val(b)));
    spl_array_free(a);
    spl_array_free(b);
}

TEST(eq_dict_same_pointer) {
    /* Same dict ptr => equal */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "k", spl_int(1));
    ASSERT(spl_eq(spl_dict_val(d), spl_dict_val(d)));
    spl_dict_free(d);
}

TEST(eq_dict_diff_pointer) {
    /* Different dict ptrs => not equal */
    SplDict* d1 = spl_dict_new();
    SplDict* d2 = spl_dict_new();
    ASSERT(!spl_eq(spl_dict_val(d1), spl_dict_val(d2)));
    spl_dict_free(d1);
    spl_dict_free(d2);
}

TEST(eq_default_unknown_tag) {
    /* Unknown tag falls through to return 0 */
    SplValue a, b;
    memset(&a, 0, sizeof(a));
    memset(&b, 0, sizeof(b));
    a.tag = (SplTag)77;
    b.tag = (SplTag)77;
    ASSERT(!spl_eq(a, b));
}

TEST(eq_different_tags) {
    /* Different tags => not equal (early return) */
    ASSERT(!spl_eq(spl_int(0), spl_float(0.0)));
    ASSERT(!spl_eq(spl_bool(0), spl_nil()));
}

/* ================================================================
 * 3. spl_to_string — Branch Coverage
 * ================================================================ */

TEST(tostring_dict) {
    /* SPL_DICT => "{...}" */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    SplValue s = spl_to_string(spl_dict_val(d));
    ASSERT_EQ_STR(spl_as_str(s), "{...}");
    spl_free_value(s);
    spl_dict_free(d);
}

TEST(tostring_null_array_ptr) {
    /* SPL_ARRAY with NULL ptr => "[]" */
    SplValue v;
    v.tag = SPL_ARRAY;
    v.as_array = NULL;
    SplValue s = spl_to_string(v);
    ASSERT_EQ_STR(spl_as_str(s), "[]");
    spl_free_value(s);
}

TEST(tostring_empty_array) {
    /* SPL_ARRAY with len==0 => "[]" */
    SplArray* a = spl_array_new();
    SplValue s = spl_to_string(spl_array_val(a));
    ASSERT_EQ_STR(spl_as_str(s), "[]");
    spl_free_value(s);
    spl_array_free(a);
}

TEST(tostring_array_buf_realloc) {
    /* Array with many long string elements forces buffer realloc past 1024 */
    SplArray* a = spl_array_new();
    /* Each element ~50 chars, 25 elements => ~1250 chars > 1024 initial buf */
    for (int i = 0; i < 25; i++) {
        spl_array_push(a, spl_str("this_is_a_long_string_to_force_buffer_realloc_xyz"));
    }
    SplValue s = spl_to_string(spl_array_val(a));
    const char* str = spl_as_str(s);
    ASSERT(str[0] == '[');
    ASSERT(strlen(str) > 1024);
    ASSERT(str[strlen(str) - 1] == ']');
    spl_free_value(s);
    spl_array_free(a);
}

TEST(tostring_unknown_tag) {
    /* Unknown tag => "?" fallback */
    SplValue v;
    memset(&v, 0, sizeof(v));
    v.tag = (SplTag)55;
    SplValue s = spl_to_string(v);
    ASSERT_EQ_STR(spl_as_str(s), "?");
    spl_free_value(s);
}

TEST(tostring_array_with_mixed_types) {
    /* Array containing different types tests recursive to_string */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_nil());
    spl_array_push(a, spl_bool(1));
    spl_array_push(a, spl_int(42));
    spl_array_push(a, spl_float(3.14));
    spl_array_push(a, spl_str("hello"));
    SplValue s = spl_to_string(spl_array_val(a));
    const char* str = spl_as_str(s);
    ASSERT(strstr(str, "nil") != NULL);
    ASSERT(strstr(str, "true") != NULL);
    ASSERT(strstr(str, "42") != NULL);
    ASSERT(strstr(str, "3.14") != NULL);
    ASSERT(strstr(str, "hello") != NULL);
    spl_free_value(s);
    spl_array_free(a);
}

/* ================================================================
 * 4. spl_free_value — Branch Coverage
 * ================================================================ */

TEST(free_value_string) {
    SplValue v = spl_str("test free");
    spl_free_value(v);  /* should free the string */
}

TEST(free_value_array) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("elem"));
    spl_free_value(spl_array_val(a));  /* should deep-free array */
}

TEST(free_value_dict) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "k", spl_str("v"));
    spl_free_value(spl_dict_val(d));  /* should deep-free dict */
}

TEST(free_value_nil) {
    spl_free_value(spl_nil());  /* default case: no-op */
}

TEST(free_value_bool) {
    spl_free_value(spl_bool(1));  /* default case: no-op */
}

TEST(free_value_int) {
    spl_free_value(spl_int(42));  /* default case: no-op */
}

TEST(free_value_float) {
    spl_free_value(spl_float(3.14));  /* default case: no-op */
}

/* ================================================================
 * 5. spl_str_slice — Branch Coverage
 * ================================================================ */

TEST(str_slice_null) {
    char* s = spl_str_slice(NULL, 0, 5);
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_slice_neg_start_clamp_to_zero) {
    /* start = -100, len = 5: -100 + 5 = -95 => clamp to 0 */
    char* s = spl_str_slice("hello", -100, 3);
    ASSERT_EQ_STR(s, "hel");
    free(s);
}

TEST(str_slice_neg_end) {
    /* end = -1 => slen + end */
    char* s = spl_str_slice("hello", 0, -1);
    ASSERT_EQ_STR(s, "hell");
    free(s);
}

TEST(str_slice_end_gt_slen) {
    /* end > slen => clamp to slen */
    char* s = spl_str_slice("hi", 0, 999);
    ASSERT_EQ_STR(s, "hi");
    free(s);
}

TEST(str_slice_start_ge_end) {
    /* start >= end => empty */
    char* s = spl_str_slice("hello", 3, 3);
    ASSERT_EQ_STR(s, "");
    free(s);

    char* s2 = spl_str_slice("hello", 4, 2);
    ASSERT_EQ_STR(s2, "");
    free(s2);
}

TEST(str_slice_neg_both) {
    /* Both negative: start=-3, end=-1 on "hello" => slice(2,4) = "ll" */
    char* s = spl_str_slice("hello", -3, -1);
    ASSERT_EQ_STR(s, "ll");
    free(s);
}

/* ================================================================
 * 6. spl_str_index_char — Branch Coverage
 * ================================================================ */

TEST(str_index_char_null) {
    char* c = spl_str_index_char(NULL, 0);
    ASSERT_EQ_STR(c, "");
    free(c);
}

TEST(str_index_char_neg_wrap) {
    /* Negative index wraps: -1 on "abc" => idx = 3 + (-1) = 2 => 'c' */
    char* c = spl_str_index_char("abc", -1);
    ASSERT_EQ_STR(c, "c");
    free(c);
}

TEST(str_index_char_neg_still_oob) {
    /* Negative index still OOB after wrap: -10 on "hi" => -10 + 2 = -8 => "" */
    char* c = spl_str_index_char("hi", -10);
    ASSERT_EQ_STR(c, "");
    free(c);
}

TEST(str_index_char_positive_oob) {
    /* Positive OOB: idx=5 on "hi" => "" */
    char* c = spl_str_index_char("hi", 5);
    ASSERT_EQ_STR(c, "");
    free(c);
}

TEST(str_index_char_valid) {
    char* c = spl_str_index_char("abcdef", 3);
    ASSERT_EQ_STR(c, "d");
    free(c);
}

/* ================================================================
 * 7. spl_str_replace — Branch Coverage
 * ================================================================ */

TEST(str_replace_null_s) {
    char* r = spl_str_replace(NULL, "a", "b");
    ASSERT_EQ_STR(r, "");
    free(r);
}

TEST(str_replace_null_old) {
    char* r = spl_str_replace("hello", NULL, "x");
    ASSERT_EQ_STR(r, "hello");
    free(r);
}

TEST(str_replace_null_new) {
    char* r = spl_str_replace("hello", "l", NULL);
    ASSERT_EQ_STR(r, "hello");
    free(r);
}

TEST(str_replace_empty_old) {
    char* r = spl_str_replace("hello", "", "x");
    ASSERT_EQ_STR(r, "hello");
    free(r);
}

TEST(str_replace_no_occurrence) {
    char* r = spl_str_replace("hello world", "xyz", "abc");
    ASSERT_EQ_STR(r, "hello world");
    free(r);
}

TEST(str_replace_multiple_occurrences) {
    char* r = spl_str_replace("aabbaabbaa", "aa", "X");
    ASSERT_EQ_STR(r, "XbbXbbX");
    free(r);
}

TEST(str_replace_longer_replacement) {
    /* Replacement longer than original */
    char* r = spl_str_replace("ab", "a", "XYZ");
    ASSERT_EQ_STR(r, "XYZb");
    free(r);
}

TEST(str_replace_shorter_replacement) {
    /* Replacement shorter than original */
    char* r = spl_str_replace("hello world hello", "hello", "hi");
    ASSERT_EQ_STR(r, "hi world hi");
    free(r);
}

TEST(str_replace_same_length) {
    char* r = spl_str_replace("cat", "cat", "dog");
    ASSERT_EQ_STR(r, "dog");
    free(r);
}

/* ================================================================
 * 8. spl_str_trim — Branch Coverage
 * ================================================================ */

TEST(str_trim_null) {
    char* s = spl_str_trim(NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_trim_empty) {
    char* s = spl_str_trim("");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_trim_all_whitespace) {
    char* s = spl_str_trim("   \t\n\r   ");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_trim_leading_mixed) {
    /* Leading \r\n\t mixed whitespace */
    char* s = spl_str_trim("\r\n\t hello");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_trim_trailing_mixed) {
    /* Trailing \r\n\t mixed whitespace */
    char* s = spl_str_trim("hello \r\n\t");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_trim_both_sides_cr) {
    char* s = spl_str_trim("\r\rhello\r\r");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_trim_no_trim_needed) {
    char* s = spl_str_trim("hello");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_trim_only_tabs) {
    char* s = spl_str_trim("\t\t\t");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_trim_inner_whitespace_kept) {
    char* s = spl_str_trim("  hello  world  ");
    ASSERT_EQ_STR(s, "hello  world");
    free(s);
}

/* ================================================================
 * 9. spl_array_push — Branch Coverage
 * ================================================================ */

TEST(array_push_null) {
    /* Push to NULL array => no-op, no crash */
    spl_array_push(NULL, spl_int(1));
}

TEST(array_push_trigger_growth) {
    /* Push more than initial capacity (16) to trigger growth */
    SplArray* a = spl_array_new();
    for (int i = 0; i < 20; i++) {
        spl_array_push(a, spl_int(i));
    }
    ASSERT_EQ_INT(spl_array_len(a), 20);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 19)), 19);
    ASSERT(a->cap >= 20);
    spl_array_free(a);
}

TEST(array_push_trigger_multiple_growths) {
    /* Force multiple resizes */
    SplArray* a = spl_array_new_cap(4);
    for (int i = 0; i < 100; i++) {
        spl_array_push(a, spl_int(i * 3));
    }
    ASSERT_EQ_INT(spl_array_len(a), 100);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 50)), 150);
    spl_array_free(a);
}

/* ================================================================
 * 10. spl_array_get — Branch Coverage
 * ================================================================ */

TEST(array_get_null) {
    SplValue v = spl_array_get(NULL, 0);
    ASSERT(v.tag == SPL_NIL);
}

TEST(array_get_neg_wrap) {
    /* Negative wrapping: -1 on [10,20,30] => items[2] = 30 */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_push(a, spl_int(20));
    spl_array_push(a, spl_int(30));
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, -1)), 30);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, -3)), 10);
    spl_array_free(a);
}

TEST(array_get_neg_still_oob) {
    /* Negative OOB after wrap: -5 on [10,20] => idx=-3 => nil */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_push(a, spl_int(20));
    ASSERT(spl_array_get(a, -5).tag == SPL_NIL);
    spl_array_free(a);
}

TEST(array_get_positive_oob) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    ASSERT(spl_array_get(a, 5).tag == SPL_NIL);
    spl_array_free(a);
}

/* ================================================================
 * 11. spl_array_set — Branch Coverage
 * ================================================================ */

TEST(array_set_null) {
    spl_array_set(NULL, 0, spl_int(1));  /* no crash */
}

TEST(array_set_neg_wrap) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_push(a, spl_int(20));
    spl_array_push(a, spl_int(30));
    spl_array_set(a, -1, spl_int(99));
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 2)), 99);
    spl_array_free(a);
}

TEST(array_set_neg_still_oob) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_set(a, -5, spl_int(99));  /* no-op */
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 10);
    spl_array_free(a);
}

TEST(array_set_positive_oob) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_set(a, 50, spl_int(99));  /* no-op */
    ASSERT_EQ_INT(spl_as_int(spl_array_get(a, 0)), 10);
    spl_array_free(a);
}

/* ================================================================
 * 12. spl_array_pop — Branch Coverage
 * ================================================================ */

TEST(array_pop_null) {
    SplValue v = spl_array_pop(NULL);
    ASSERT(v.tag == SPL_NIL);
}

TEST(array_pop_empty) {
    SplArray* a = spl_array_new();
    SplValue v = spl_array_pop(a);
    ASSERT(v.tag == SPL_NIL);
    spl_array_free(a);
}

TEST(array_pop_nonempty) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(42));
    spl_array_push(a, spl_int(99));
    SplValue v = spl_array_pop(a);
    ASSERT_EQ_INT(spl_as_int(v), 99);
    ASSERT_EQ_INT(spl_array_len(a), 1);
    spl_array_free(a);
}

/* ================================================================
 * 13. spl_array_slice — Branch Coverage
 * ================================================================ */

TEST(array_slice_null) {
    SplArray* s = spl_array_slice(NULL, 0, 5);
    ASSERT_EQ_INT(spl_array_len(s), 0);
    spl_array_free(s);
}

TEST(array_slice_neg_indices) {
    SplArray* a = spl_array_new();
    for (int i = 0; i < 5; i++) spl_array_push(a, spl_int(i));
    /* -3, -1 on len=5 => slice(2, 4) => [2, 3] */
    SplArray* s = spl_array_slice(a, -3, -1);
    ASSERT_EQ_INT(spl_array_len(s), 2);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(s, 0)), 2);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(s, 1)), 3);
    free(s->items); free(s);
    spl_array_free(a);
}

TEST(array_slice_empty_range) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    /* start >= end */
    SplArray* s = spl_array_slice(a, 1, 0);
    ASSERT_EQ_INT(spl_array_len(s), 0);
    spl_array_free(s);
    spl_array_free(a);
}

TEST(array_slice_end_gt_len) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_push(a, spl_int(20));
    /* end=100 > len=2 => clamp to 2 */
    SplArray* s = spl_array_slice(a, 0, 100);
    ASSERT_EQ_INT(spl_array_len(s), 2);
    free(s->items); free(s);
    spl_array_free(a);
}

TEST(array_slice_start_clamp_to_zero) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(10));
    spl_array_push(a, spl_int(20));
    /* start=-100 => -100+2=-98 => clamp to 0 */
    SplArray* s = spl_array_slice(a, -100, 2);
    ASSERT_EQ_INT(spl_array_len(s), 2);
    free(s->items); free(s);
    spl_array_free(a);
}

/* ================================================================
 * 14. spl_array_concat — Branch Coverage
 * ================================================================ */

TEST(array_concat_null_a) {
    SplArray* b = spl_array_new();
    spl_array_push(b, spl_int(1));
    SplArray* r = spl_array_concat(NULL, b);
    ASSERT_EQ_INT(spl_array_len(r), 1);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(r, 0)), 1);
    free(r->items); free(r);
    spl_array_free(b);
}

TEST(array_concat_null_b) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    SplArray* r = spl_array_concat(a, NULL);
    ASSERT_EQ_INT(spl_array_len(r), 1);
    free(r->items); free(r);
    spl_array_free(a);
}

TEST(array_concat_both_null) {
    SplArray* r = spl_array_concat(NULL, NULL);
    ASSERT_EQ_INT(spl_array_len(r), 0);
    free(r->items); free(r);
}

TEST(array_concat_both_nonempty) {
    SplArray* a = spl_array_new();
    SplArray* b = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_int(2));
    spl_array_push(b, spl_int(3));
    spl_array_push(b, spl_int(4));
    SplArray* r = spl_array_concat(a, b);
    ASSERT_EQ_INT(spl_array_len(r), 4);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(r, 0)), 1);
    ASSERT_EQ_INT(spl_as_int(spl_array_get(r, 3)), 4);
    free(r->items); free(r);
    spl_array_free(a);
    spl_array_free(b);
}

/* ================================================================
 * 15. spl_array_free — Branch Coverage
 * ================================================================ */

TEST(array_free_null) {
    spl_array_free(NULL);  /* no crash */
}

TEST(array_free_with_strings) {
    /* Deep free: array elements that are strings must be freed */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("string1"));
    spl_array_push(a, spl_str("string2"));
    spl_array_push(a, spl_str("string3"));
    spl_array_free(a);  /* should free all string elements */
}

TEST(array_free_with_nested_array) {
    /* Deep free nested array */
    SplArray* inner = spl_array_new();
    spl_array_push(inner, spl_int(1));
    SplArray* outer = spl_array_new();
    spl_array_push(outer, spl_array_val(inner));
    spl_array_free(outer);  /* should free inner too */
}

/* ================================================================
 * 16. spl_dict_set — Branch Coverage
 * ================================================================ */

TEST(dict_set_null_dict) {
    spl_dict_set(NULL, "k", spl_int(1));  /* no crash */
}

TEST(dict_set_null_key) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, NULL, spl_int(1));  /* no-op */
    ASSERT_EQ_INT(spl_dict_len(d), 0);
    spl_dict_free(d);
}

TEST(dict_set_trigger_resize) {
    /* Start with cap=4, insert enough to exceed 70% load factor */
    SplDict* d = spl_dict_new_cap(4);
    /* Cap is 4. Load factor 0.70 => threshold ~2.8. Insert 3 should trigger resize. */
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_set(d, "b", spl_int(2));
    spl_dict_set(d, "c", spl_int(3));
    ASSERT(d->cap > 4);  /* should have resized */
    ASSERT_EQ_INT(spl_dict_len(d), 3);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "a")), 1);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "b")), 2);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "c")), 3);
    spl_dict_free(d);
}

TEST(dict_set_insert_empty_slot) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "key1", spl_int(100));
    ASSERT_EQ_INT(spl_dict_len(d), 1);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "key1")), 100);
    spl_dict_free(d);
}

TEST(dict_set_insert_tombstone) {
    /* Create a tombstone then insert over it */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "key1", spl_int(1));
    spl_dict_set(d, "key2", spl_int(2));
    spl_dict_remove(d, "key1");
    ASSERT_EQ_INT(d->tombstones, 1);
    /* Re-insert might hit that tombstone slot */
    spl_dict_set(d, "key1", spl_int(10));
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "key1")), 10);
    ASSERT_EQ_INT(spl_dict_len(d), 2);
    spl_dict_free(d);
}

TEST(dict_set_update_existing) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "k", spl_int(1));
    spl_dict_set(d, "k", spl_int(2));  /* update */
    ASSERT_EQ_INT(spl_dict_len(d), 1);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "k")), 2);
    spl_dict_free(d);
}

/* ================================================================
 * 17. spl_dict_find — Branch Coverage
 * ================================================================ */

TEST(dict_find_empty_dict) {
    /* len==0 => returns NULL immediately */
    SplDict* d = spl_dict_new();
    SplValue v = spl_dict_get(d, "missing");
    ASSERT(v.tag == SPL_NIL);
    spl_dict_free(d);
}

TEST(dict_find_probe_past_tombstone) {
    /* Remove creates tombstone; find must probe past it */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_set(d, "b", spl_int(2));
    spl_dict_set(d, "c", spl_int(3));
    spl_dict_remove(d, "a");
    /* Finding "b" or "c" may need to probe past the tombstone at "a"'s slot */
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "b")), 2);
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "c")), 3);
    spl_dict_free(d);
}

TEST(dict_find_key_not_found) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "x", spl_int(1));
    ASSERT(!spl_dict_contains(d, "y"));
    SplValue v = spl_dict_get(d, "y");
    ASSERT(v.tag == SPL_NIL);
    spl_dict_free(d);
}

TEST(dict_find_hash_collision_probe) {
    /* Force collision: plant a decoy with same hash at target slot.
     * Use a large enough cap that inserting "target" won't trigger a resize.
     * The decoy has the same hash as "target" but a different key,
     * forcing the probe logic to skip past it. */
    SplDict* d = spl_dict_new_cap(64);
    uint64_t h = spl_str_hash("target");
    int64_t slot = (int64_t)(h & (uint64_t)(d->cap - 1));

    /* Plant decoy at slot with same hash but different key */
    d->entries[slot].key = strdup("decoy");
    d->entries[slot].value = spl_int(100);
    d->entries[slot].hash = h;  /* same hash as "target"! */
    d->entries[slot].occupied = 1;
    d->len = 1;

    /* dict_set("target") finds decoy: hash matches, strcmp differs => probe past */
    spl_dict_set(d, "target", spl_int(200));
    ASSERT_EQ_INT(d->len, 2);

    /* "target" should be findable at the probed slot */
    ASSERT_EQ_INT(spl_as_int(spl_dict_get(d, "target")), 200);

    /* Verify the decoy is still at the original slot (direct access, not via API
     * since spl_dict_get("decoy") hashes "decoy" which maps to a different slot) */
    ASSERT(d->entries[slot].occupied == 1);
    ASSERT_EQ_STR(d->entries[slot].key, "decoy");
    ASSERT_EQ_INT(spl_as_int(d->entries[slot].value), 100);

    spl_dict_free(d);
}

/* ================================================================
 * 18. spl_dict_remove — Branch Coverage
 * ================================================================ */

TEST(dict_remove_existing) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "k", spl_int(42));
    spl_dict_remove(d, "k");
    ASSERT_EQ_INT(spl_dict_len(d), 0);
    ASSERT_EQ_INT(d->tombstones, 1);
    ASSERT(!spl_dict_contains(d, "k"));
    spl_dict_free(d);
}

TEST(dict_remove_nonexistent) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_remove(d, "missing");  /* no-op */
    ASSERT_EQ_INT(spl_dict_len(d), 1);
    spl_dict_free(d);
}

TEST(dict_remove_from_null) {
    spl_dict_remove(NULL, "k");  /* no crash (dict_find returns NULL) */
}

/* ================================================================
 * 19. spl_dict_keys/values — Branch Coverage
 * ================================================================ */

TEST(dict_keys_null) {
    SplArray* keys = spl_dict_keys(NULL);
    ASSERT_EQ_INT(spl_array_len(keys), 0);
    spl_array_free(keys);
}

TEST(dict_keys_with_tombstones) {
    /* Dict with tombstones: only occupied==1 entries appear */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_set(d, "b", spl_int(2));
    spl_dict_set(d, "c", spl_int(3));
    spl_dict_remove(d, "b");  /* tombstone */
    SplArray* keys = spl_dict_keys(d);
    ASSERT_EQ_INT(spl_array_len(keys), 2);
    spl_array_free(keys);
    spl_dict_free(d);
}

TEST(dict_values_null) {
    SplArray* vals = spl_dict_values(NULL);
    ASSERT_EQ_INT(spl_array_len(vals), 0);
    spl_array_free(vals);
}

TEST(dict_values_with_tombstones) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "x", spl_int(10));
    spl_dict_set(d, "y", spl_int(20));
    spl_dict_set(d, "z", spl_int(30));
    spl_dict_remove(d, "y");
    SplArray* vals = spl_dict_values(d);
    ASSERT_EQ_INT(spl_array_len(vals), 2);
    /* Sum should be 10 + 30 = 40 */
    int64_t sum = 0;
    for (int64_t i = 0; i < spl_array_len(vals); i++) {
        sum += spl_as_int(spl_array_get(vals, i));
    }
    ASSERT_EQ_INT(sum, 40);
    free(vals->items); free(vals);
    spl_dict_free(d);
}

/* ================================================================
 * 20. spl_dict_free — Branch Coverage
 * ================================================================ */

TEST(dict_free_null) {
    spl_dict_free(NULL);  /* no crash */
}

TEST(dict_free_with_entries) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "s1", spl_str("value1"));
    spl_dict_set(d, "s2", spl_str("value2"));
    spl_dict_free(d);  /* frees keys and string values */
}

TEST(dict_free_with_tombstones) {
    /* Tombstone entries (occupied==-1) should not be freed */
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_set(d, "b", spl_int(2));
    spl_dict_remove(d, "a");  /* tombstone */
    spl_dict_free(d);  /* should not double-free */
}

/* ================================================================
 * 21. spl_file_read — Branch Coverage
 * ================================================================ */

TEST(file_read_null_path) {
    char* c = spl_file_read(NULL);
    ASSERT_EQ_STR(c, "");
    free(c);
}

TEST(file_read_nonexistent) {
    char* c = spl_file_read(TMP_PREFIX "nonexistent_xyz_12345.txt");
    ASSERT_EQ_STR(c, "");
    free(c);
}

TEST(file_read_existing) {
    const char* path = TMP_PREFIX "read_test.txt";
    spl_file_write(path, "read content");
    char* c = spl_file_read(path);
    ASSERT_EQ_STR(c, "read content");
    free(c);
    remove(path);
}

/* ================================================================
 * 22. spl_file_write — Branch Coverage
 * ================================================================ */

TEST(file_write_null_path) {
    ASSERT(!spl_file_write(NULL, "test"));
}

TEST(file_write_null_content) {
    const char* path = TMP_PREFIX "write_null.txt";
    ASSERT(spl_file_write(path, NULL));
    char* c = spl_file_read(path);
    ASSERT_EQ_STR(c, "");
    free(c);
    remove(path);
}

TEST(file_write_valid) {
    const char* path = TMP_PREFIX "write_valid.txt";
    ASSERT(spl_file_write(path, "written data"));
    char* c = spl_file_read(path);
    ASSERT_EQ_STR(c, "written data");
    free(c);
    remove(path);
}

TEST(file_write_invalid_dir) {
    /* fopen fails => returns 0 */
#ifdef _WIN32
    ASSERT(!spl_file_write("Z:\\nonexistent_dir_12345\\file.txt", "test"));
#else
    ASSERT(!spl_file_write("/nonexistent_dir_12345/file.txt", "test"));
#endif
}

/* ================================================================
 * 23. spl_file_append — Branch Coverage
 * ================================================================ */

TEST(file_append_null_path) {
    ASSERT(!spl_file_append(NULL, "test"));
}

TEST(file_append_null_content) {
    const char* path = TMP_PREFIX "append_null.txt";
    spl_file_write(path, "base");
    ASSERT(spl_file_append(path, NULL));
    char* c = spl_file_read(path);
    ASSERT_EQ_STR(c, "base");
    free(c);
    remove(path);
}

TEST(file_append_valid) {
    const char* path = TMP_PREFIX "append_valid.txt";
    spl_file_write(path, "line1");
    spl_file_append(path, "\nline2");
    char* c = spl_file_read(path);
    ASSERT_EQ_STR(c, "line1\nline2");
    free(c);
    remove(path);
}

TEST(file_append_invalid_dir) {
#ifdef _WIN32
    ASSERT(!spl_file_append("Z:\\nonexistent_dir_12345\\file.txt", "test"));
#else
    ASSERT(!spl_file_append("/nonexistent_dir_12345/file.txt", "test"));
#endif
}

/* ================================================================
 * 24. spl_file_exists — Branch Coverage
 * ================================================================ */

TEST(file_exists_null) {
    ASSERT(!spl_file_exists(NULL));
}

TEST(file_exists_nonexistent) {
    ASSERT(!spl_file_exists(TMP_PREFIX "nonexistent_xyz_12345.txt"));
}

TEST(file_exists_existing) {
    const char* path = TMP_PREFIX "exists_test.txt";
    spl_file_write(path, "x");
    ASSERT(spl_file_exists(path));
    remove(path);
}

/* ================================================================
 * 25. spl_shell — Branch Coverage
 * ================================================================ */

TEST(shell_null_cmd) {
    ASSERT_EQ_INT(spl_shell(NULL), -1);
}

TEST(shell_valid_cmd) {
#ifdef _WIN32
    int64_t rc = spl_shell("cmd /c echo hello > NUL");
#else
    int64_t rc = spl_shell("true");
#endif
    ASSERT_EQ_INT(rc, 0);
}

/* ================================================================
 * 26. spl_shell_output — Branch Coverage
 * ================================================================ */

TEST(shell_output_null_cmd) {
    char* out = spl_shell_output(NULL);
    ASSERT_EQ_STR(out, "");
    free(out);
}

TEST(shell_output_valid_cmd) {
#ifdef _WIN32
    char* out = spl_shell_output("cmd /c echo hello");
#else
    char* out = spl_shell_output("echo hello");
#endif
    ASSERT(strlen(out) > 0);
    ASSERT(strstr(out, "hello") != NULL);
    free(out);
}

TEST(shell_output_large_buffer_realloc) {
    /* Force realloc in spl_shell_output by producing large output */
#ifdef _WIN32
    char* out = spl_shell_output("cmd /c \"for /L %i in (1,1,500) do @echo line_%i\"");
#else
    char* out = spl_shell_output("seq 1 2000");
#endif
    ASSERT(strlen(out) > 0);
    free(out);
}

/* ================================================================
 * 27. spl_env_get — Branch Coverage
 * ================================================================ */

TEST(env_get_null_key) {
    ASSERT_EQ_STR(spl_env_get(NULL), "");
}

TEST(env_get_nonexistent_key) {
    ASSERT_EQ_STR(spl_env_get("SPL_DEFINITELY_NOT_SET_99999"), "");
}

TEST(env_get_existing_key) {
    spl_env_set("SPL_BRANCH_TEST_KEY", "branch_val");
    ASSERT_EQ_STR(spl_env_get("SPL_BRANCH_TEST_KEY"), "branch_val");
    spl_env_set("SPL_BRANCH_TEST_KEY", NULL);  /* clean up */
}

/* ================================================================
 * 28. spl_env_set — Branch Coverage
 * ================================================================ */

TEST(env_set_null_key) {
    spl_env_set(NULL, "value");  /* no-op, no crash */
}

TEST(env_set_null_value) {
    spl_env_set("SPL_BRANCH_TEST_UNSET", "temp");
    spl_env_set("SPL_BRANCH_TEST_UNSET", NULL);  /* unset on Unix, set empty on Win */
    /* After unset, should return "" */
    ASSERT_EQ_STR(spl_env_get("SPL_BRANCH_TEST_UNSET"), "");
}

TEST(env_set_valid) {
    spl_env_set("SPL_BRANCH_TEST_SET", "myval");
    ASSERT_EQ_STR(spl_env_get("SPL_BRANCH_TEST_SET"), "myval");
    spl_env_set("SPL_BRANCH_TEST_SET", NULL);
}

/* ================================================================
 * 29. spl_get_arg — Branch Coverage
 * ================================================================ */

TEST(get_arg_negative_idx) {
    char* argv[] = {"prog", "arg1"};
    spl_init_args(2, argv);
    ASSERT_EQ_STR(spl_get_arg(-1), "");
}

TEST(get_arg_oob_idx) {
    char* argv[] = {"prog"};
    spl_init_args(1, argv);
    ASSERT_EQ_STR(spl_get_arg(5), "");
}

TEST(get_arg_valid_idx) {
    char* argv[] = {"prog", "first", "second"};
    spl_init_args(3, argv);
    ASSERT_EQ_STR(spl_get_arg(0), "prog");
    ASSERT_EQ_STR(spl_get_arg(1), "first");
    ASSERT_EQ_STR(spl_get_arg(2), "second");
}

TEST(get_arg_null_entry) {
    char* argv[] = {"prog", NULL, "arg2"};
    spl_init_args(3, argv);
    ASSERT_EQ_STR(spl_get_arg(1), "");
    spl_init_args(0, NULL);
}

/* ================================================================
 * 30. spl_sprintf — Branch Coverage
 * ================================================================ */

TEST(sprintf_valid) {
    char* s = spl_sprintf("hello %s %d", "world", 42);
    ASSERT_EQ_STR(s, "hello world 42");
    free(s);
}

TEST(sprintf_empty_format) {
    char* s = spl_sprintf("");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(sprintf_long_output) {
    /* Force large output */
    char* s = spl_sprintf("%s%s%s%s%s", "aaaa", "bbbb", "cccc", "dddd", "eeee");
    ASSERT_EQ_STR(s, "aaaabbbbccccddddeeee");
    free(s);
}

/* ================================================================
 * 31. spl_strdup — Branch Coverage
 * ================================================================ */

TEST(strdup_null) {
    char* s = spl_strdup(NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(strdup_valid) {
    char* s = spl_strdup("hello");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(strdup_empty) {
    char* s = spl_strdup("");
    ASSERT_EQ_STR(s, "");
    free(s);
}

/* ================================================================
 * 32. spl_array_new_cap — Branch Coverage
 * ================================================================ */

TEST(array_new_cap_small) {
    /* cap < 4 should clamp to 4 */
    SplArray* a = spl_array_new_cap(1);
    ASSERT(a->cap >= 4);
    spl_array_free(a);
}

TEST(array_new_cap_zero) {
    SplArray* a = spl_array_new_cap(0);
    ASSERT(a->cap >= 4);
    spl_array_free(a);
}

TEST(array_new_cap_negative) {
    SplArray* a = spl_array_new_cap(-5);
    ASSERT(a->cap >= 4);
    spl_array_free(a);
}

TEST(array_new_cap_large) {
    SplArray* a = spl_array_new_cap(100);
    ASSERT(a->cap >= 100);
    spl_array_free(a);
}

/* ================================================================
 * 33. Typed array helpers — Branch Coverage
 * ================================================================ */

TEST(typed_push_i64) {
    SplArray* a = spl_array_new_i64();
    spl_array_push_i64(a, 10);
    spl_array_push_i64(a, 20);
    ASSERT_EQ_INT(spl_array_len(a), 2);
    spl_array_free(a);
}

TEST(typed_get_i64) {
    SplArray* a = spl_array_new_i64();
    spl_array_push_i64(a, 42);
    ASSERT_EQ_INT(spl_array_get_i64(a, 0), 42);
    spl_array_free(a);
}

TEST(typed_set_i64) {
    SplArray* a = spl_array_new_i64();
    spl_array_push_i64(a, 10);
    spl_array_set_i64(a, 0, 99);
    ASSERT_EQ_INT(spl_array_get_i64(a, 0), 99);
    spl_array_free(a);
}

TEST(typed_push_text) {
    SplArray* a = spl_array_new_text();
    spl_array_push_text(a, "hello");
    spl_array_push_text(a, "world");
    ASSERT_EQ_INT(spl_array_len(a), 2);
    spl_array_free(a);
}

TEST(typed_get_text) {
    SplArray* a = spl_array_new_text();
    spl_array_push_text(a, "test");
    ASSERT_EQ_STR(spl_array_get_text(a, 0), "test");
    spl_array_free(a);
}

TEST(typed_i64_negative_index) {
    SplArray* a = spl_array_new_i64();
    spl_array_push_i64(a, 10);
    spl_array_push_i64(a, 20);
    /* get_i64 with negative index uses spl_array_get which wraps */
    ASSERT_EQ_INT(spl_array_get_i64(a, -1), 20);
    spl_array_free(a);
}

TEST(typed_text_oob) {
    SplArray* a = spl_array_new_text();
    spl_array_push_text(a, "only");
    /* OOB returns nil, spl_as_str on nil returns "" */
    ASSERT_EQ_STR(spl_array_get_text(a, 5), "");
    spl_array_free(a);
}

/* ================================================================
 * 34. spl_dict_new_cap — Branch Coverage
 * ================================================================ */

TEST(dict_new_cap_small) {
    /* cap=1 should round up to 4 (power of 2 >= 4) */
    SplDict* d = spl_dict_new_cap(1);
    ASSERT(d->cap >= 4);
    spl_dict_free(d);
}

TEST(dict_new_cap_not_power_of_two) {
    /* cap=5 should round up to 8 */
    SplDict* d = spl_dict_new_cap(5);
    ASSERT(d->cap == 8);
    spl_dict_free(d);
}

TEST(dict_new_cap_exact_power_of_two) {
    /* cap=8 should stay 8 */
    SplDict* d = spl_dict_new_cap(8);
    ASSERT(d->cap == 8);
    spl_dict_free(d);
}

TEST(dict_new_cap_larger) {
    /* cap=100 should round up to 128 */
    SplDict* d = spl_dict_new_cap(100);
    ASSERT(d->cap == 128);
    spl_dict_free(d);
}

/* ================================================================
 * 35. spl_wffi_call_i64 — Branch Coverage
 * ================================================================ */

static int64_t wffi_fn0(void) { return 100; }
static int64_t wffi_fn1(int64_t a) { return a * 2; }
static int64_t wffi_fn2(int64_t a, int64_t b) { return a + b; }
static int64_t wffi_fn3(int64_t a, int64_t b, int64_t c) { return a + b + c; }
static int64_t wffi_fn4(int64_t a, int64_t b, int64_t c, int64_t d) { return a * b + c * d; }

TEST(wffi_null_fptr) {
    int64_t args[1] = {0};
    ASSERT_EQ_INT(spl_wffi_call_i64(NULL, args, 0), 0);
    ASSERT_EQ_INT(spl_wffi_call_i64(NULL, args, 1), 0);
}

TEST(wffi_0_args) {
    int64_t args[1] = {0};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)wffi_fn0, args, 0), 100);
}

TEST(wffi_1_arg) {
    int64_t args[1] = {7};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)wffi_fn1, args, 1), 14);
}

TEST(wffi_2_args) {
    int64_t args[2] = {10, 20};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)wffi_fn2, args, 2), 30);
}

TEST(wffi_3_args) {
    int64_t args[3] = {1, 2, 3};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)wffi_fn3, args, 3), 6);
}

TEST(wffi_4_args) {
    int64_t args[4] = {2, 3, 4, 5};
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)wffi_fn4, args, 4), 26); /* 2*3 + 4*5 = 26 */
}

TEST(wffi_invalid_nargs) {
    int64_t args[5] = {1, 2, 3, 4, 5};
    /* nargs=5 hits default case => returns 0 */
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)wffi_fn0, args, 5), 0);
    /* nargs=-1 also hits default */
    ASSERT_EQ_INT(spl_wffi_call_i64((void*)wffi_fn0, args, -1), 0);
}

/* ================================================================
 * Additional branch coverage: str_eq, str_cmp with NULL
 * ================================================================ */

TEST(str_eq_both_null) {
    ASSERT(spl_str_eq(NULL, NULL));
}

TEST(str_eq_one_null) {
    ASSERT(!spl_str_eq("abc", NULL));
    ASSERT(!spl_str_eq(NULL, "abc"));
}

TEST(str_cmp_null_a) {
    ASSERT(spl_str_cmp(NULL, "abc") < 0);
}

TEST(str_cmp_null_b) {
    ASSERT(spl_str_cmp("abc", NULL) > 0);
}

TEST(str_cmp_both_null) {
    ASSERT_EQ_INT(spl_str_cmp(NULL, NULL), 0);
}

/* ================================================================
 * Additional: str_contains, starts_with, ends_with NULL branches
 * ================================================================ */

TEST(str_contains_null_s) {
    ASSERT(!spl_str_contains(NULL, "x"));
}

TEST(str_contains_null_needle) {
    ASSERT(!spl_str_contains("hello", NULL));
}

TEST(str_starts_with_null_s) {
    ASSERT(!spl_str_starts_with(NULL, "x"));
}

TEST(str_starts_with_null_prefix) {
    ASSERT(!spl_str_starts_with("hello", NULL));
}

TEST(str_ends_with_null_s) {
    ASSERT(!spl_str_ends_with(NULL, "x"));
}

TEST(str_ends_with_null_suffix) {
    ASSERT(!spl_str_ends_with("hello", NULL));
}

TEST(str_ends_with_longer_suffix) {
    /* suflen > slen => 0 */
    ASSERT(!spl_str_ends_with("hi", "much_longer_suffix"));
}

/* ================================================================
 * Additional: str_index_of NULL branches
 * ================================================================ */

TEST(str_index_of_null_s) {
    ASSERT_EQ_INT(spl_str_index_of(NULL, "x"), -1);
}

TEST(str_index_of_null_needle) {
    ASSERT_EQ_INT(spl_str_index_of("hello", NULL), -1);
}

TEST(str_index_of_not_found) {
    ASSERT_EQ_INT(spl_str_index_of("hello", "xyz"), -1);
}

/* ================================================================
 * Additional: str_to_upper, str_to_lower NULL branches
 * ================================================================ */

TEST(str_to_upper_null) {
    char* s = spl_str_to_upper(NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_to_lower_null) {
    char* s = spl_str_to_lower(NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

/* ================================================================
 * Additional: str_hash NULL branch
 * ================================================================ */

TEST(str_hash_null) {
    uint64_t h = spl_str_hash(NULL);
    /* Returns base FNV hash */
    ASSERT(h != 0);
}

TEST(str_hash_empty) {
    uint64_t h = spl_str_hash("");
    ASSERT(h != 0);
}

/* ================================================================
 * Additional: spl_str_new NULL branch
 * ================================================================ */

TEST(str_new_null) {
    char* s = spl_str_new(NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

/* ================================================================
 * Additional: spl_str_concat NULL branches
 * ================================================================ */

TEST(str_concat_null_a) {
    char* s = spl_str_concat(NULL, "world");
    ASSERT_EQ_STR(s, "world");
    free(s);
}

TEST(str_concat_null_b) {
    char* s = spl_str_concat("hello", NULL);
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(str_concat_both_null) {
    char* s = spl_str_concat(NULL, NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

/* ================================================================
 * Additional: dict_contains NULL branches
 * ================================================================ */

TEST(dict_contains_null_dict) {
    ASSERT(!spl_dict_contains(NULL, "k"));
}

TEST(dict_contains_null_key) {
    SplDict* d = spl_dict_new();
    ASSERT(!spl_dict_contains(d, NULL));
    spl_dict_free(d);
}

/* ================================================================
 * Additional: dict resize with many tombstones
 * ================================================================ */

TEST(dict_resize_tombstones_cleaned) {
    /* After resize, tombstones should be gone */
    SplDict* d = spl_dict_new_cap(4);
    spl_dict_set(d, "a", spl_int(1));
    spl_dict_set(d, "b", spl_int(2));
    spl_dict_remove(d, "a");
    ASSERT_EQ_INT(d->tombstones, 1);
    /* Force resize by adding enough entries */
    spl_dict_set(d, "c", spl_int(3));
    spl_dict_set(d, "d", spl_int(4));
    spl_dict_set(d, "e", spl_int(5));
    /* After resize, tombstones should be 0 */
    ASSERT_EQ_INT(d->tombstones, 0);
    /* All entries except "a" should be present */
    ASSERT(!spl_dict_contains(d, "a"));
    ASSERT(spl_dict_contains(d, "b"));
    ASSERT(spl_dict_contains(d, "e"));
    spl_dict_free(d);
}

/* ================================================================
 * Additional: spl_array_len NULL
 * ================================================================ */

TEST(array_len_null) {
    ASSERT_EQ_INT(spl_array_len(NULL), 0);
}

/* ================================================================
 * Additional: spl_dict_len NULL
 * ================================================================ */

TEST(dict_len_null) {
    ASSERT_EQ_INT(spl_dict_len(NULL), 0);
}

/* ================================================================
 * Additional: spl_str constructor branches
 * ================================================================ */

TEST(spl_str_null_input) {
    SplValue v = spl_str(NULL);
    ASSERT_EQ_STR(spl_as_str(v), "");
    spl_free_value(v);
}

TEST(spl_str_own_null_input) {
    SplValue v = spl_str_own(NULL);
    ASSERT_EQ_STR(spl_as_str(v), "");
    spl_free_value(v);
}

/* ================================================================
 * Additional: spl_as_str with NULL as_str
 * ================================================================ */

TEST(as_str_null_ptr) {
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = NULL;
    ASSERT_EQ_STR(spl_as_str(v), "");
}

/* ================================================================
 * Additional: Print functions (no crash)
 * ================================================================ */

TEST(print_null) {
    spl_print(NULL);   /* no crash, no output */
    spl_println(NULL); /* prints just newline */
}

/* ================================================================
 * Additional: spl_malloc / spl_free
 * ================================================================ */

TEST(malloc_and_free) {
    void* p = spl_malloc(64);
    ASSERT_NOT_NULL(p);
    memset(p, 0xAA, 64);
    spl_free(p);
}

TEST(free_null) {
    spl_free(NULL);  /* no crash */
}

/* ================================================================
 * Additional: spl_bool normalization
 * ================================================================ */

TEST(bool_normalization) {
    /* Non-zero values should normalize to 1 */
    SplValue v = spl_bool(42);
    ASSERT_EQ_INT(spl_as_bool(v), 1);
    SplValue v2 = spl_bool(-1);
    ASSERT_EQ_INT(spl_as_bool(v2), 1);
}

/* ================================================================
 * 36. spl_str_last_index_of — Branch Coverage
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
    /* empty needle => needle_len==0 => -1 */
    ASSERT_EQ_INT(spl_str_last_index_of("hello", ""), -1);
}

TEST(last_index_of_needle_longer_than_s) {
    /* needle_len > slen => -1 */
    ASSERT_EQ_INT(spl_str_last_index_of("hi", "hello world"), -1);
}

TEST(last_index_of_not_found) {
    ASSERT_EQ_INT(spl_str_last_index_of("hello world", "xyz"), -1);
}

TEST(last_index_of_single_occurrence) {
    ASSERT_EQ_INT(spl_str_last_index_of("hello world", "world"), 6);
}

TEST(last_index_of_multiple_occurrences) {
    /* Should return LAST occurrence */
    ASSERT_EQ_INT(spl_str_last_index_of("abcabc", "abc"), 3);
}

TEST(last_index_of_at_start) {
    ASSERT_EQ_INT(spl_str_last_index_of("abc", "abc"), 0);
}

TEST(last_index_of_at_end) {
    ASSERT_EQ_INT(spl_str_last_index_of("xxabc", "abc"), 2);
}

TEST(last_index_of_single_char) {
    /* "banana" last index of "a" => 5 */
    ASSERT_EQ_INT(spl_str_last_index_of("banana", "a"), 5);
}

TEST(last_index_of_overlapping) {
    /* "aaa" last index of "aa" => 1 (starts scanning from end) */
    ASSERT_EQ_INT(spl_str_last_index_of("aaa", "aa"), 1);
}

TEST(last_index_of_exact_match) {
    ASSERT_EQ_INT(spl_str_last_index_of("abc", "abc"), 0);
}

/* ================================================================
 * 37. spl_array_contains_str — Branch Coverage
 * ================================================================ */

TEST(array_contains_str_null_arr) {
    ASSERT(!spl_array_contains_str(NULL, "hello"));
}

TEST(array_contains_str_null_needle) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("hello"));
    ASSERT(!spl_array_contains_str(a, NULL));
    spl_array_free(a);
}

TEST(array_contains_str_both_null) {
    ASSERT(!spl_array_contains_str(NULL, NULL));
}

TEST(array_contains_str_empty_array) {
    SplArray* a = spl_array_new();
    ASSERT(!spl_array_contains_str(a, "hello"));
    spl_array_free(a);
}

TEST(array_contains_str_found) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("apple"));
    spl_array_push(a, spl_str("banana"));
    spl_array_push(a, spl_str("cherry"));
    ASSERT(spl_array_contains_str(a, "banana"));
    spl_array_free(a);
}

TEST(array_contains_str_not_found) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("apple"));
    spl_array_push(a, spl_str("banana"));
    ASSERT(!spl_array_contains_str(a, "cherry"));
    spl_array_free(a);
}

TEST(array_contains_str_non_string_elements) {
    /* Array with non-string elements should skip them */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(42));
    spl_array_push(a, spl_bool(1));
    spl_array_push(a, spl_nil());
    ASSERT(!spl_array_contains_str(a, "42"));
    spl_array_free(a);
}

TEST(array_contains_str_mixed_types) {
    /* Mix of string and non-string, string is present */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(1));
    spl_array_push(a, spl_str("target"));
    spl_array_push(a, spl_float(3.14));
    ASSERT(spl_array_contains_str(a, "target"));
    spl_array_free(a);
}

TEST(array_contains_str_null_str_element) {
    /* Array with a SPL_STRING whose as_str is NULL */
    SplArray* a = spl_array_new();
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = NULL;
    spl_array_push(a, v);
    ASSERT(!spl_array_contains_str(a, "hello"));
    spl_array_free(a);
}

TEST(array_contains_str_empty_needle) {
    /* Empty string needle, with empty string in array */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str(""));
    ASSERT(spl_array_contains_str(a, ""));
    spl_array_free(a);
}

/* ================================================================
 * 38. spl_str_split — Branch Coverage
 * ================================================================ */

TEST(str_split_null_s) {
    SplArray* arr = spl_str_split(NULL, ",");
    ASSERT_EQ_INT(spl_array_len(arr), 0);
    spl_array_free(arr);
}

TEST(str_split_null_delim) {
    /* NULL delim => return array with original string as sole element */
    SplArray* arr = spl_str_split("hello,world", NULL);
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "hello,world");
    spl_array_free(arr);
}

TEST(str_split_empty_delim) {
    /* Empty delim => return array with original string as sole element */
    SplArray* arr = spl_str_split("hello,world", "");
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "hello,world");
    spl_array_free(arr);
}

TEST(str_split_basic) {
    SplArray* arr = spl_str_split("a,b,c", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "a");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "b");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 2)), "c");
    spl_array_free(arr);
}

TEST(str_split_no_delim_found) {
    /* Delimiter not present => single element array */
    SplArray* arr = spl_str_split("hello", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "hello");
    spl_array_free(arr);
}

TEST(str_split_delim_at_start) {
    /* Delimiter at start => first element is empty string */
    SplArray* arr = spl_str_split(",hello", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 2);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "hello");
    spl_array_free(arr);
}

TEST(str_split_delim_at_end) {
    /* Delimiter at end => last element is empty string */
    SplArray* arr = spl_str_split("hello,", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 2);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "hello");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "");
    spl_array_free(arr);
}

TEST(str_split_consecutive_delimiters) {
    /* Consecutive delimiters => empty strings between them */
    SplArray* arr = spl_str_split("a,,b", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "a");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 2)), "b");
    spl_array_free(arr);
}

TEST(str_split_multi_char_delim) {
    SplArray* arr = spl_str_split("one::two::three", "::");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "one");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "two");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 2)), "three");
    spl_array_free(arr);
}

TEST(str_split_empty_string) {
    /* Empty string split by any delim => [""] */
    SplArray* arr = spl_str_split("", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 1);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "");
    spl_array_free(arr);
}

TEST(str_split_only_delimiters) {
    /* String is only delimiters => empty strings */
    SplArray* arr = spl_str_split(",,", ",");
    ASSERT_EQ_INT(spl_array_len(arr), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 0)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 1)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(arr, 2)), "");
    spl_array_free(arr);
}

/* ================================================================
 * 39. spl_str_join — Branch Coverage
 * ================================================================ */

TEST(str_join_null_arr) {
    char* s = spl_str_join(NULL, ",");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(str_join_empty_arr) {
    SplArray* a = spl_array_new();
    char* s = spl_str_join(a, ",");
    ASSERT_EQ_STR(s, "");
    free(s);
    spl_array_free(a);
}

TEST(str_join_null_delim) {
    /* NULL delim => treated as "" */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("a"));
    spl_array_push(a, spl_str("b"));
    char* s = spl_str_join(a, NULL);
    ASSERT_EQ_STR(s, "ab");
    free(s);
    spl_array_free(a);
}

TEST(str_join_basic) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("hello"));
    spl_array_push(a, spl_str("world"));
    char* s = spl_str_join(a, " ");
    ASSERT_EQ_STR(s, "hello world");
    free(s);
    spl_array_free(a);
}

TEST(str_join_single_element) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("only"));
    char* s = spl_str_join(a, ",");
    ASSERT_EQ_STR(s, "only");
    free(s);
    spl_array_free(a);
}

TEST(str_join_multi_char_delim) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("a"));
    spl_array_push(a, spl_str("b"));
    spl_array_push(a, spl_str("c"));
    char* s = spl_str_join(a, " :: ");
    ASSERT_EQ_STR(s, "a :: b :: c");
    free(s);
    spl_array_free(a);
}

TEST(str_join_empty_delim) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str("x"));
    spl_array_push(a, spl_str("y"));
    spl_array_push(a, spl_str("z"));
    char* s = spl_str_join(a, "");
    ASSERT_EQ_STR(s, "xyz");
    free(s);
    spl_array_free(a);
}

TEST(str_join_non_string_items) {
    /* Non-string items in array should be treated as "" */
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(42));
    spl_array_push(a, spl_str("hello"));
    spl_array_push(a, spl_bool(1));
    char* s = spl_str_join(a, ",");
    ASSERT_EQ_STR(s, ",hello,");
    free(s);
    spl_array_free(a);
}

TEST(str_join_null_str_element) {
    /* SPL_STRING with NULL as_str => treated as "" */
    SplArray* a = spl_array_new();
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = NULL;
    spl_array_push(a, v);
    spl_array_push(a, spl_str("ok"));
    char* s = spl_str_join(a, "-");
    ASSERT_EQ_STR(s, "-ok");
    free(s);
    spl_array_free(a);
}

TEST(str_join_empty_strings) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_str(""));
    spl_array_push(a, spl_str(""));
    spl_array_push(a, spl_str(""));
    char* s = spl_str_join(a, ",");
    ASSERT_EQ_STR(s, ",,");
    free(s);
    spl_array_free(a);
}

/* ================================================================
 * 40. spl_file_delete — Branch Coverage
 * ================================================================ */

TEST(file_delete_null_path) {
    ASSERT_EQ_INT(spl_file_delete(NULL), 0);
}

TEST(file_delete_nonexistent) {
    ASSERT_EQ_INT(spl_file_delete(TMP_PREFIX "nonexistent_del_12345.txt"), 0);
}

TEST(file_delete_existing) {
    const char* path = TMP_PREFIX "delete_test.txt";
    spl_file_write(path, "to be deleted");
    ASSERT(spl_file_exists(path));
    ASSERT_EQ_INT(spl_file_delete(path), 1);
    ASSERT(!spl_file_exists(path));
}

/* ================================================================
 * 41. spl_file_size — Branch Coverage
 * ================================================================ */

TEST(file_size_null_path) {
    ASSERT_EQ_INT(spl_file_size(NULL), -1);
}

TEST(file_size_nonexistent) {
    ASSERT_EQ_INT(spl_file_size(TMP_PREFIX "nonexistent_size_12345.txt"), -1);
}

TEST(file_size_empty_file) {
    const char* path = TMP_PREFIX "size_empty.txt";
    spl_file_write(path, "");
    ASSERT_EQ_INT(spl_file_size(path), 0);
    remove(path);
}

TEST(file_size_nonempty_file) {
    const char* path = TMP_PREFIX "size_test.txt";
    spl_file_write(path, "hello");  /* 5 bytes */
    ASSERT_EQ_INT(spl_file_size(path), 5);
    remove(path);
}

TEST(file_size_larger_file) {
    const char* path = TMP_PREFIX "size_large.txt";
    /* Write 100 'A' characters */
    char buf[101];
    memset(buf, 'A', 100);
    buf[100] = '\0';
    spl_file_write(path, buf);
    ASSERT_EQ_INT(spl_file_size(path), 100);
    remove(path);
}

/* ================================================================
 * 42. rt_ wrapper aliases — Branch Coverage
 * ================================================================ */

TEST(rt_file_read_text_valid) {
    const char* path = TMP_PREFIX "rt_read.txt";
    spl_file_write(path, "rt content");
    const char* c = rt_file_read_text(path);
    ASSERT_EQ_STR(c, "rt content");
    /* rt_file_read_text returns spl_file_read result (heap-allocated) */
    free((void*)c);
    remove(path);
}

TEST(rt_file_read_text_null) {
    const char* c = rt_file_read_text(NULL);
    ASSERT_EQ_STR(c, "");
    free((void*)c);
}

TEST(rt_file_exists_true) {
    const char* path = TMP_PREFIX "rt_exists.txt";
    spl_file_write(path, "x");
    ASSERT(rt_file_exists(path));
    remove(path);
}

TEST(rt_file_exists_false) {
    ASSERT(!rt_file_exists(TMP_PREFIX "rt_nonexist_12345.txt"));
}

TEST(rt_file_write_valid) {
    const char* path = TMP_PREFIX "rt_write.txt";
    rt_file_write(path, "rt written");
    ASSERT(spl_file_exists(path));
    char* c = spl_file_read(path);
    ASSERT_EQ_STR(c, "rt written");
    free(c);
    remove(path);
}

TEST(rt_file_write_null_path) {
    /* void function - no return value to check */
    rt_file_write(NULL, "test");
}

TEST(rt_file_delete_valid) {
    const char* path = TMP_PREFIX "rt_delete.txt";
    spl_file_write(path, "to delete");
    ASSERT_EQ_INT(rt_file_delete(path), 1);
    ASSERT(!spl_file_exists(path));
}

TEST(rt_file_delete_null) {
    ASSERT_EQ_INT(rt_file_delete(NULL), 0);
}

TEST(rt_file_size_valid) {
    const char* path = TMP_PREFIX "rt_size.txt";
    spl_file_write(path, "abc");
    ASSERT_EQ_INT(rt_file_size(path), 3);
    remove(path);
}

TEST(rt_file_size_null) {
    ASSERT_EQ_INT(rt_file_size(NULL), -1);
}

/* ================================================================
 * 43. rt_shell_output — Branch Coverage
 * ================================================================ */

TEST(rt_shell_output_valid) {
#ifdef _WIN32
    const char* out = rt_shell_output("cmd /c echo rt_hello");
#else
    const char* out = rt_shell_output("echo rt_hello");
#endif
    ASSERT(strstr(out, "rt_hello") != NULL);
    free((void*)out);
}

TEST(rt_shell_output_null) {
    const char* out = rt_shell_output(NULL);
    ASSERT_EQ_STR(out, "");
    free((void*)out);
}

/* ================================================================
 * 44. rt_cli_get_args — Branch Coverage
 * ================================================================ */

TEST(rt_cli_get_args_with_args) {
    char* argv[] = {"myapp", "arg1", "arg2"};
    spl_init_args(3, argv);
    SplArray* args = rt_cli_get_args();
    ASSERT_EQ_INT(spl_array_len(args), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 0)), "myapp");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 1)), "arg1");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 2)), "arg2");
    spl_array_free(args);
}

TEST(rt_cli_get_args_empty) {
    spl_init_args(0, NULL);
    SplArray* args = rt_cli_get_args();
    ASSERT_EQ_INT(spl_array_len(args), 0);
    spl_array_free(args);
}

TEST(rt_cli_get_args_null_entry) {
    /* g_argv with NULL entry => should produce "" for that element */
    char* argv[] = {"prog", NULL, "arg2"};
    spl_init_args(3, argv);
    SplArray* args = rt_cli_get_args();
    ASSERT_EQ_INT(spl_array_len(args), 3);
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 0)), "prog");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 1)), "");
    ASSERT_EQ_STR(spl_as_str(spl_array_get(args, 2)), "arg2");
    spl_array_free(args);
    spl_init_args(0, NULL);
}

/* ================================================================
 * 45. spl_str_split + spl_str_join roundtrip
 * ================================================================ */

TEST(split_join_roundtrip) {
    const char* original = "hello world foo bar";
    SplArray* parts = spl_str_split(original, " ");
    ASSERT_EQ_INT(spl_array_len(parts), 4);
    char* joined = spl_str_join(parts, " ");
    ASSERT_EQ_STR(joined, original);
    free(joined);
    spl_array_free(parts);
}

TEST(split_join_roundtrip_multi_delim) {
    const char* original = "a::b::c";
    SplArray* parts = spl_str_split(original, "::");
    ASSERT_EQ_INT(spl_array_len(parts), 3);
    char* joined = spl_str_join(parts, "::");
    ASSERT_EQ_STR(joined, original);
    free(joined);
    spl_array_free(parts);
}

/* ================================================================
 * 46. Uncovered accessor functions
 * ================================================================ */

TEST(as_float_basic) {
    SplValue v = spl_float(3.14);
    ASSERT(spl_as_float(v) > 3.13 && spl_as_float(v) < 3.15);
}

TEST(as_array_basic) {
    SplArray* a = spl_array_new();
    spl_array_push(a, spl_int(42));
    SplValue v = spl_array_val(a);
    SplArray* got = spl_as_array(v);
    ASSERT(got != NULL);
    ASSERT_EQ_INT(spl_array_len(got), 1);
    spl_array_free(got);
}

TEST(as_dict_basic) {
    SplDict* d = spl_dict_new();
    spl_dict_set(d, "key", spl_int(1));
    SplValue v = spl_dict_val(d);
    SplDict* got = spl_as_dict(v);
    ASSERT(got != NULL);
    ASSERT_EQ_INT(spl_dict_len(got), 1);
    spl_dict_free(got);
}

/* ================================================================
 * 47. spl_str_len — Branch Coverage
 * ================================================================ */

TEST(str_len_null) {
    ASSERT_EQ_INT(spl_str_len(NULL), 0);
}

TEST(str_len_empty) {
    ASSERT_EQ_INT(spl_str_len(""), 0);
}

TEST(str_len_nonempty) {
    ASSERT_EQ_INT(spl_str_len("hello"), 5);
}

/* ================================================================
 * 48. spl_str_to_upper / spl_str_to_lower — full coverage
 * ================================================================ */

TEST(str_to_upper_basic) {
    char* r = spl_str_to_upper("hello");
    ASSERT_EQ_STR(r, "HELLO");
    free(r);
}

TEST(str_to_upper_mixed) {
    char* r = spl_str_to_upper("Hello World 123!");
    ASSERT_EQ_STR(r, "HELLO WORLD 123!");
    free(r);
}

TEST(str_to_upper_empty) {
    char* r = spl_str_to_upper("");
    ASSERT_EQ_STR(r, "");
    free(r);
}

TEST(str_to_lower_basic) {
    char* r = spl_str_to_lower("HELLO");
    ASSERT_EQ_STR(r, "hello");
    free(r);
}

TEST(str_to_lower_mixed) {
    char* r = spl_str_to_lower("Hello World 123!");
    ASSERT_EQ_STR(r, "hello world 123!");
    free(r);
}

TEST(str_to_lower_empty) {
    char* r = spl_str_to_lower("");
    ASSERT_EQ_STR(r, "");
    free(r);
}

/* ================================================================
 * 49. spl_print_i64 / spl_print_f64 — Branch Coverage
 * ================================================================ */

TEST(print_i64_basic) {
    /* Just call it — we can't capture stdout but this exercises the function */
    spl_print_i64(42);
    spl_print_i64(-1);
    spl_print_i64(0);
    /* If we get here without crash, it's OK */
}

TEST(print_f64_basic) {
    spl_print_f64(3.14);
    spl_print_f64(-0.5);
    spl_print_f64(0.0);
}

/* ================================================================
 * 50. spl_arg_count — Branch Coverage
 * ================================================================ */

TEST(arg_count_zero) {
    spl_init_args(0, NULL);
    ASSERT_EQ_INT(spl_arg_count(), 0);
}

TEST(arg_count_nonzero) {
    char* argv[] = {"prog", "a", "b"};
    spl_init_args(3, argv);
    ASSERT_EQ_INT(spl_arg_count(), 3);
    spl_init_args(0, NULL);
}

/* ================================================================
 * 51. rt_exec_manager stubs — Branch Coverage
 * ================================================================ */

TEST(exec_manager_create) {
    int64_t h = rt_exec_manager_create("test");
    ASSERT_EQ_INT(h, 0);
}

TEST(exec_manager_compile) {
    const char* r = rt_exec_manager_compile(0, "mir_data");
    ASSERT_EQ_STR(r, "");
}

TEST(exec_manager_execute) {
    int64_t r = rt_exec_manager_execute(0, "func", NULL);
    ASSERT_EQ_INT(r, 0);
}

TEST(exec_manager_has_function) {
    ASSERT(!rt_exec_manager_has_function(0, "func"));
}

TEST(exec_manager_cleanup) {
    rt_exec_manager_cleanup(0);
    /* No crash = pass */
}

/* ================================================================
 * 52. spl_is_truthy float/bool edge cases
 * ================================================================ */

TEST(truthy_float_zero) {
    ASSERT(!spl_is_truthy(spl_float(0.0)));
}

TEST(truthy_float_nonzero) {
    ASSERT(spl_is_truthy(spl_float(0.001)));
}

TEST(truthy_bool_false) {
    ASSERT(!spl_is_truthy(spl_bool(0)));
}

TEST(truthy_bool_true) {
    ASSERT(spl_is_truthy(spl_bool(1)));
}

TEST(truthy_int_zero) {
    ASSERT(!spl_is_truthy(spl_int(0)));
}

TEST(truthy_int_nonzero) {
    ASSERT(spl_is_truthy(spl_int(42)));
}

TEST(truthy_nil) {
    ASSERT(!spl_is_truthy(spl_nil()));
}

/* ================================================================
 * 53. spl_eq additional branches (float, nil, string NULL)
 * ================================================================ */

TEST(eq_nil_nil) {
    ASSERT(spl_eq(spl_nil(), spl_nil()));
}

TEST(eq_bool_same) {
    ASSERT(spl_eq(spl_bool(1), spl_bool(1)));
}

TEST(eq_bool_diff) {
    ASSERT(!spl_eq(spl_bool(1), spl_bool(0)));
}

TEST(eq_float_same) {
    ASSERT(spl_eq(spl_float(3.14), spl_float(3.14)));
}

TEST(eq_float_diff) {
    ASSERT(!spl_eq(spl_float(3.14), spl_float(2.71)));
}

TEST(eq_string_null_null) {
    SplValue a, b;
    a.tag = SPL_STRING; a.as_str = NULL;
    b.tag = SPL_STRING; b.as_str = NULL;
    ASSERT(spl_eq(a, b));
}

TEST(eq_string_null_vs_empty) {
    SplValue a, b;
    a.tag = SPL_STRING; a.as_str = NULL;
    b = spl_str("");
    ASSERT(spl_eq(a, b));
    spl_free_value(b);
}

TEST(eq_int_same) {
    ASSERT(spl_eq(spl_int(100), spl_int(100)));
}

TEST(eq_int_diff) {
    ASSERT(!spl_eq(spl_int(100), spl_int(200)));
}

/* ================================================================
 * 54. spl_str_contains/starts_with/ends_with/index_of - non-NULL success
 * ================================================================ */

TEST(str_contains_found) {
    ASSERT(spl_str_contains("hello world", "world"));
}

TEST(str_contains_not_found) {
    ASSERT(!spl_str_contains("hello world", "xyz"));
}

TEST(str_starts_with_true) {
    ASSERT(spl_str_starts_with("hello world", "hello"));
}

TEST(str_starts_with_false) {
    ASSERT(!spl_str_starts_with("hello world", "world"));
}

TEST(str_ends_with_true) {
    ASSERT(spl_str_ends_with("hello world", "world"));
}

TEST(str_ends_with_false) {
    ASSERT(!spl_str_ends_with("hello world", "hello"));
}

TEST(str_index_of_found) {
    ASSERT_EQ_INT(spl_str_index_of("hello world", "world"), 6);
}

/* ================================================================
 * 55. spl_print / spl_println non-null
 * ================================================================ */

TEST(print_notnull) {
    spl_print("x");  /* exercises the non-NULL branch */
}

TEST(println_notnull) {
    spl_println("y");  /* exercises the non-NULL branch */
}

TEST(println_null) {
    spl_println(NULL);  /* exercises the NULL s branch — still prints \n */
}

/* ================================================================
 * 56. spl_str_new non-null
 * ================================================================ */

TEST(str_new_notnull) {
    char* r = spl_str_new("hello");
    ASSERT_EQ_STR(r, "hello");
    free(r);
}

/* ================================================================
 * Main
 * ================================================================ */

int main(void) {
    printf("=== Runtime Branch Coverage Tests ===\n\n");

    printf("--- 1. spl_is_truthy branches ---\n");
    RUN(truthy_array_null_ptr);
    RUN(truthy_array_empty);
    RUN(truthy_array_nonempty);
    RUN(truthy_dict_null_ptr);
    RUN(truthy_dict_empty);
    RUN(truthy_dict_nonempty);
    RUN(truthy_string_null_ptr);
    RUN(truthy_string_empty);
    RUN(truthy_string_nonempty);
    RUN(truthy_default_unknown_tag);

    printf("\n--- 2. spl_eq branches ---\n");
    RUN(eq_array_both_null);
    RUN(eq_array_one_null_left);
    RUN(eq_array_one_null_right);
    RUN(eq_array_same_pointer);
    RUN(eq_array_matching_elements);
    RUN(eq_array_diff_length);
    RUN(eq_array_same_len_diff_elem);
    RUN(eq_dict_same_pointer);
    RUN(eq_dict_diff_pointer);
    RUN(eq_default_unknown_tag);
    RUN(eq_different_tags);

    printf("\n--- 3. spl_to_string branches ---\n");
    RUN(tostring_dict);
    RUN(tostring_null_array_ptr);
    RUN(tostring_empty_array);
    RUN(tostring_array_buf_realloc);
    RUN(tostring_unknown_tag);
    RUN(tostring_array_with_mixed_types);

    printf("\n--- 4. spl_free_value branches ---\n");
    RUN(free_value_string);
    RUN(free_value_array);
    RUN(free_value_dict);
    RUN(free_value_nil);
    RUN(free_value_bool);
    RUN(free_value_int);
    RUN(free_value_float);

    printf("\n--- 5. spl_str_slice branches ---\n");
    RUN(str_slice_null);
    RUN(str_slice_neg_start_clamp_to_zero);
    RUN(str_slice_neg_end);
    RUN(str_slice_end_gt_slen);
    RUN(str_slice_start_ge_end);
    RUN(str_slice_neg_both);

    printf("\n--- 6. spl_str_index_char branches ---\n");
    RUN(str_index_char_null);
    RUN(str_index_char_neg_wrap);
    RUN(str_index_char_neg_still_oob);
    RUN(str_index_char_positive_oob);
    RUN(str_index_char_valid);

    printf("\n--- 7. spl_str_replace branches ---\n");
    RUN(str_replace_null_s);
    RUN(str_replace_null_old);
    RUN(str_replace_null_new);
    RUN(str_replace_empty_old);
    RUN(str_replace_no_occurrence);
    RUN(str_replace_multiple_occurrences);
    RUN(str_replace_longer_replacement);
    RUN(str_replace_shorter_replacement);
    RUN(str_replace_same_length);

    printf("\n--- 8. spl_str_trim branches ---\n");
    RUN(str_trim_null);
    RUN(str_trim_empty);
    RUN(str_trim_all_whitespace);
    RUN(str_trim_leading_mixed);
    RUN(str_trim_trailing_mixed);
    RUN(str_trim_both_sides_cr);
    RUN(str_trim_no_trim_needed);
    RUN(str_trim_only_tabs);
    RUN(str_trim_inner_whitespace_kept);

    printf("\n--- 9. spl_array_push branches ---\n");
    RUN(array_push_null);
    RUN(array_push_trigger_growth);
    RUN(array_push_trigger_multiple_growths);

    printf("\n--- 10. spl_array_get branches ---\n");
    RUN(array_get_null);
    RUN(array_get_neg_wrap);
    RUN(array_get_neg_still_oob);
    RUN(array_get_positive_oob);

    printf("\n--- 11. spl_array_set branches ---\n");
    RUN(array_set_null);
    RUN(array_set_neg_wrap);
    RUN(array_set_neg_still_oob);
    RUN(array_set_positive_oob);

    printf("\n--- 12. spl_array_pop branches ---\n");
    RUN(array_pop_null);
    RUN(array_pop_empty);
    RUN(array_pop_nonempty);

    printf("\n--- 13. spl_array_slice branches ---\n");
    RUN(array_slice_null);
    RUN(array_slice_neg_indices);
    RUN(array_slice_empty_range);
    RUN(array_slice_end_gt_len);
    RUN(array_slice_start_clamp_to_zero);

    printf("\n--- 14. spl_array_concat branches ---\n");
    RUN(array_concat_null_a);
    RUN(array_concat_null_b);
    RUN(array_concat_both_null);
    RUN(array_concat_both_nonempty);

    printf("\n--- 15. spl_array_free branches ---\n");
    RUN(array_free_null);
    RUN(array_free_with_strings);
    RUN(array_free_with_nested_array);

    printf("\n--- 16. spl_dict_set branches ---\n");
    RUN(dict_set_null_dict);
    RUN(dict_set_null_key);
    RUN(dict_set_trigger_resize);
    RUN(dict_set_insert_empty_slot);
    RUN(dict_set_insert_tombstone);
    RUN(dict_set_update_existing);

    printf("\n--- 17. spl_dict_find branches ---\n");
    RUN(dict_find_empty_dict);
    RUN(dict_find_probe_past_tombstone);
    RUN(dict_find_key_not_found);
    RUN(dict_find_hash_collision_probe);

    printf("\n--- 18. spl_dict_remove branches ---\n");
    RUN(dict_remove_existing);
    RUN(dict_remove_nonexistent);
    RUN(dict_remove_from_null);

    printf("\n--- 19. spl_dict_keys/values branches ---\n");
    RUN(dict_keys_null);
    RUN(dict_keys_with_tombstones);
    RUN(dict_values_null);
    RUN(dict_values_with_tombstones);

    printf("\n--- 20. spl_dict_free branches ---\n");
    RUN(dict_free_null);
    RUN(dict_free_with_entries);
    RUN(dict_free_with_tombstones);

    printf("\n--- 21. spl_file_read branches ---\n");
    RUN(file_read_null_path);
    RUN(file_read_nonexistent);
    RUN(file_read_existing);

    printf("\n--- 22. spl_file_write branches ---\n");
    RUN(file_write_null_path);
    RUN(file_write_null_content);
    RUN(file_write_valid);
    RUN(file_write_invalid_dir);

    printf("\n--- 23. spl_file_append branches ---\n");
    RUN(file_append_null_path);
    RUN(file_append_null_content);
    RUN(file_append_valid);
    RUN(file_append_invalid_dir);

    printf("\n--- 24. spl_file_exists branches ---\n");
    RUN(file_exists_null);
    RUN(file_exists_nonexistent);
    RUN(file_exists_existing);

    printf("\n--- 25. spl_shell branches ---\n");
    RUN(shell_null_cmd);
    RUN(shell_valid_cmd);

    printf("\n--- 26. spl_shell_output branches ---\n");
    RUN(shell_output_null_cmd);
    RUN(shell_output_valid_cmd);
    RUN(shell_output_large_buffer_realloc);

    printf("\n--- 27. spl_env_get branches ---\n");
    RUN(env_get_null_key);
    RUN(env_get_nonexistent_key);
    RUN(env_get_existing_key);

    printf("\n--- 28. spl_env_set branches ---\n");
    RUN(env_set_null_key);
    RUN(env_set_null_value);
    RUN(env_set_valid);

    printf("\n--- 29. spl_get_arg branches ---\n");
    RUN(get_arg_negative_idx);
    RUN(get_arg_oob_idx);
    RUN(get_arg_valid_idx);
    RUN(get_arg_null_entry);

    printf("\n--- 30. spl_sprintf branches ---\n");
    RUN(sprintf_valid);
    RUN(sprintf_empty_format);
    RUN(sprintf_long_output);

    printf("\n--- 31. spl_strdup branches ---\n");
    RUN(strdup_null);
    RUN(strdup_valid);
    RUN(strdup_empty);

    printf("\n--- 32. spl_array_new_cap branches ---\n");
    RUN(array_new_cap_small);
    RUN(array_new_cap_zero);
    RUN(array_new_cap_negative);
    RUN(array_new_cap_large);

    printf("\n--- 33. Typed array helpers ---\n");
    RUN(typed_push_i64);
    RUN(typed_get_i64);
    RUN(typed_set_i64);
    RUN(typed_push_text);
    RUN(typed_get_text);
    RUN(typed_i64_negative_index);
    RUN(typed_text_oob);

    printf("\n--- 34. spl_dict_new_cap branches ---\n");
    RUN(dict_new_cap_small);
    RUN(dict_new_cap_not_power_of_two);
    RUN(dict_new_cap_exact_power_of_two);
    RUN(dict_new_cap_larger);

    printf("\n--- 35. spl_wffi_call_i64 branches ---\n");
    RUN(wffi_null_fptr);
    RUN(wffi_0_args);
    RUN(wffi_1_arg);
    RUN(wffi_2_args);
    RUN(wffi_3_args);
    RUN(wffi_4_args);
    RUN(wffi_invalid_nargs);

    printf("\n--- String NULL branches ---\n");
    RUN(str_eq_both_null);
    RUN(str_eq_one_null);
    RUN(str_cmp_null_a);
    RUN(str_cmp_null_b);
    RUN(str_cmp_both_null);
    RUN(str_contains_null_s);
    RUN(str_contains_null_needle);
    RUN(str_starts_with_null_s);
    RUN(str_starts_with_null_prefix);
    RUN(str_ends_with_null_s);
    RUN(str_ends_with_null_suffix);
    RUN(str_ends_with_longer_suffix);
    RUN(str_index_of_null_s);
    RUN(str_index_of_null_needle);
    RUN(str_index_of_not_found);
    RUN(str_to_upper_null);
    RUN(str_to_lower_null);
    RUN(str_hash_null);
    RUN(str_hash_empty);
    RUN(str_new_null);
    RUN(str_concat_null_a);
    RUN(str_concat_null_b);
    RUN(str_concat_both_null);

    printf("\n--- Dict NULL branches ---\n");
    RUN(dict_contains_null_dict);
    RUN(dict_contains_null_key);
    RUN(dict_resize_tombstones_cleaned);

    printf("\n--- Misc branches ---\n");
    RUN(array_len_null);
    RUN(dict_len_null);
    RUN(spl_str_null_input);
    RUN(spl_str_own_null_input);
    RUN(as_str_null_ptr);
    RUN(print_null);
    RUN(malloc_and_free);
    RUN(free_null);
    RUN(bool_normalization);

    printf("\n--- 36. spl_str_last_index_of branches ---\n");
    RUN(last_index_of_null_s);
    RUN(last_index_of_null_needle);
    RUN(last_index_of_both_null);
    RUN(last_index_of_empty_needle);
    RUN(last_index_of_needle_longer_than_s);
    RUN(last_index_of_not_found);
    RUN(last_index_of_single_occurrence);
    RUN(last_index_of_multiple_occurrences);
    RUN(last_index_of_at_start);
    RUN(last_index_of_at_end);
    RUN(last_index_of_single_char);
    RUN(last_index_of_overlapping);
    RUN(last_index_of_exact_match);

    printf("\n--- 37. spl_array_contains_str branches ---\n");
    RUN(array_contains_str_null_arr);
    RUN(array_contains_str_null_needle);
    RUN(array_contains_str_both_null);
    RUN(array_contains_str_empty_array);
    RUN(array_contains_str_found);
    RUN(array_contains_str_not_found);
    RUN(array_contains_str_non_string_elements);
    RUN(array_contains_str_mixed_types);
    RUN(array_contains_str_null_str_element);
    RUN(array_contains_str_empty_needle);

    printf("\n--- 38. spl_str_split branches ---\n");
    RUN(str_split_null_s);
    RUN(str_split_null_delim);
    RUN(str_split_empty_delim);
    RUN(str_split_basic);
    RUN(str_split_no_delim_found);
    RUN(str_split_delim_at_start);
    RUN(str_split_delim_at_end);
    RUN(str_split_consecutive_delimiters);
    RUN(str_split_multi_char_delim);
    RUN(str_split_empty_string);
    RUN(str_split_only_delimiters);

    printf("\n--- 39. spl_str_join branches ---\n");
    RUN(str_join_null_arr);
    RUN(str_join_empty_arr);
    RUN(str_join_null_delim);
    RUN(str_join_basic);
    RUN(str_join_single_element);
    RUN(str_join_multi_char_delim);
    RUN(str_join_empty_delim);
    RUN(str_join_non_string_items);
    RUN(str_join_null_str_element);
    RUN(str_join_empty_strings);

    printf("\n--- 40. spl_file_delete branches ---\n");
    RUN(file_delete_null_path);
    RUN(file_delete_nonexistent);
    RUN(file_delete_existing);

    printf("\n--- 41. spl_file_size branches ---\n");
    RUN(file_size_null_path);
    RUN(file_size_nonexistent);
    RUN(file_size_empty_file);
    RUN(file_size_nonempty_file);
    RUN(file_size_larger_file);

    printf("\n--- 42. rt_ wrapper aliases ---\n");
    RUN(rt_file_read_text_valid);
    RUN(rt_file_read_text_null);
    RUN(rt_file_exists_true);
    RUN(rt_file_exists_false);
    RUN(rt_file_write_valid);
    RUN(rt_file_write_null_path);
    RUN(rt_file_delete_valid);
    RUN(rt_file_delete_null);
    RUN(rt_file_size_valid);
    RUN(rt_file_size_null);

    printf("\n--- 43. rt_shell_output branches ---\n");
    RUN(rt_shell_output_valid);
    RUN(rt_shell_output_null);

    printf("\n--- 44. rt_cli_get_args branches ---\n");
    RUN(rt_cli_get_args_with_args);
    RUN(rt_cli_get_args_empty);
    RUN(rt_cli_get_args_null_entry);

    printf("\n--- 45. split/join roundtrip ---\n");
    RUN(split_join_roundtrip);
    RUN(split_join_roundtrip_multi_delim);

    printf("\n--- 46. Uncovered accessor functions ---\n");
    RUN(as_float_basic);
    RUN(as_array_basic);
    RUN(as_dict_basic);

    printf("\n--- 47. spl_str_len ---\n");
    RUN(str_len_null);
    RUN(str_len_empty);
    RUN(str_len_nonempty);

    printf("\n--- 48. spl_str_to_upper/lower full ---\n");
    RUN(str_to_upper_basic);
    RUN(str_to_upper_mixed);
    RUN(str_to_upper_empty);
    RUN(str_to_lower_basic);
    RUN(str_to_lower_mixed);
    RUN(str_to_lower_empty);

    printf("\n--- 49. spl_print_i64/f64 ---\n");
    RUN(print_i64_basic);
    RUN(print_f64_basic);

    printf("\n--- 50. spl_arg_count ---\n");
    RUN(arg_count_zero);
    RUN(arg_count_nonzero);

    printf("\n--- 51. rt_exec_manager stubs ---\n");
    RUN(exec_manager_create);
    RUN(exec_manager_compile);
    RUN(exec_manager_execute);
    RUN(exec_manager_has_function);
    RUN(exec_manager_cleanup);

    printf("\n--- 52. spl_is_truthy extra ---\n");
    RUN(truthy_float_zero);
    RUN(truthy_float_nonzero);
    RUN(truthy_bool_false);
    RUN(truthy_bool_true);
    RUN(truthy_int_zero);
    RUN(truthy_int_nonzero);
    RUN(truthy_nil);

    printf("\n--- 53. spl_eq extra ---\n");
    RUN(eq_nil_nil);
    RUN(eq_bool_same);
    RUN(eq_bool_diff);
    RUN(eq_float_same);
    RUN(eq_float_diff);
    RUN(eq_string_null_null);
    RUN(eq_string_null_vs_empty);
    RUN(eq_int_same);
    RUN(eq_int_diff);

    printf("\n--- 54. String search ops ---\n");
    RUN(str_contains_found);
    RUN(str_contains_not_found);
    RUN(str_starts_with_true);
    RUN(str_starts_with_false);
    RUN(str_ends_with_true);
    RUN(str_ends_with_false);
    RUN(str_index_of_found);

    printf("\n--- 55. spl_print/println ---\n");
    RUN(print_notnull);
    RUN(println_notnull);
    RUN(println_null);

    printf("\n--- 56. spl_str_new ---\n");
    RUN(str_new_notnull);

    printf("\n=== All %d tests passed ===\n", tests_run);
    return 0;
}
