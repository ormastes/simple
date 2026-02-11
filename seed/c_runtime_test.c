/*
 * c_runtime.c — Test Suite
 *
 * Tests the static helper functions from src/app/compile/c_runtime.c.
 * Since c_runtime.c uses static functions, we #include it directly.
 *
 * Build:
 *   cc -o /tmp/c_runtime_test bootstrap/c_runtime_test.c -std=c11 -Wall && /tmp/c_runtime_test
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Include the static functions directly */
#include "../src/app/compile/c_runtime.c"

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
    long long _a = (long long)(a), _b = (long long)(b); \
    if (_a != _b) { \
        printf(" FAIL\n    %lld != %lld\n    %s:%d\n", _a, _b, __FILE__, __LINE__); \
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
 * simple_strlen tests
 * ================================================================ */

TEST(strlen_basic) {
    ASSERT_EQ_INT(simple_strlen("hello"), 5);
    ASSERT_EQ_INT(simple_strlen(""), 0);
    ASSERT_EQ_INT(simple_strlen(NULL), 0);
}

/* ================================================================
 * simple_substring tests
 * ================================================================ */

TEST(substring_basic) {
    char* s = simple_substring("hello world", 0, 5);
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(substring_middle) {
    char* s = simple_substring("hello world", 6, 11);
    ASSERT_EQ_STR(s, "world");
    free(s);
}

TEST(substring_null) {
    char* s = simple_substring(NULL, 0, 5);
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(substring_clamp) {
    char* s = simple_substring("hello", -5, 100);
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(substring_empty_range) {
    char* s = simple_substring("hello", 3, 3);
    ASSERT_EQ_STR(s, "");
    free(s);

    char* s2 = simple_substring("hello", 5, 3);
    ASSERT_EQ_STR(s2, "");
    free(s2);
}

/* ================================================================
 * simple_contains tests
 * ================================================================ */

TEST(contains_basic) {
    ASSERT(simple_contains("hello world", "world"));
    ASSERT(simple_contains("hello world", "hello"));
    ASSERT(!simple_contains("hello world", "xyz"));
    ASSERT(simple_contains("abc", ""));
}

TEST(contains_null) {
    ASSERT(!simple_contains(NULL, "x"));
    ASSERT(!simple_contains("x", NULL));
    ASSERT(!simple_contains(NULL, NULL));
}

/* ================================================================
 * simple_starts_with / simple_ends_with tests
 * ================================================================ */

TEST(starts_with_basic) {
    ASSERT(simple_starts_with("hello world", "hello"));
    ASSERT(!simple_starts_with("hello world", "world"));
    ASSERT(simple_starts_with("abc", ""));
}

TEST(starts_with_null) {
    ASSERT(!simple_starts_with(NULL, "x"));
    ASSERT(!simple_starts_with("x", NULL));
}

TEST(ends_with_basic) {
    ASSERT(simple_ends_with("hello world", "world"));
    ASSERT(!simple_ends_with("hello world", "hello"));
    ASSERT(simple_ends_with("abc", ""));
}

TEST(ends_with_null) {
    ASSERT(!simple_ends_with(NULL, "x"));
    ASSERT(!simple_ends_with("x", NULL));
}

TEST(ends_with_longer_suffix) {
    ASSERT(!simple_ends_with("hi", "longer_than_string"));
}

/* ================================================================
 * simple_trim tests
 * ================================================================ */

TEST(trim_basic) {
    char* s = simple_trim("  hello  ");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(trim_tabs_newlines) {
    char* s = simple_trim("\t\n hello \r\n");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(trim_null) {
    char* s = simple_trim(NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(trim_empty) {
    char* s = simple_trim("");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(trim_all_whitespace) {
    char* s = simple_trim("   \t\n\r   ");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(trim_no_whitespace) {
    char* s = simple_trim("hello");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

/* ================================================================
 * simple_index_of tests
 * ================================================================ */

TEST(index_of_basic) {
    ASSERT_EQ_INT(simple_index_of("hello world", "world"), 6);
    ASSERT_EQ_INT(simple_index_of("hello world", "xyz"), -1);
    ASSERT_EQ_INT(simple_index_of("hello", ""), 0);
}

TEST(index_of_null) {
    ASSERT_EQ_INT(simple_index_of(NULL, "x"), -1);
    ASSERT_EQ_INT(simple_index_of("x", NULL), -1);
}

/* ================================================================
 * simple_last_index_of tests
 * ================================================================ */

TEST(last_index_of_basic) {
    ASSERT_EQ_INT(simple_last_index_of("hello world hello", "hello"), 12);
    ASSERT_EQ_INT(simple_last_index_of("hello world", "world"), 6);
    ASSERT_EQ_INT(simple_last_index_of("hello", "xyz"), -1);
}

TEST(last_index_of_null) {
    ASSERT_EQ_INT(simple_last_index_of(NULL, "x"), -1);
    ASSERT_EQ_INT(simple_last_index_of("x", NULL), -1);
}

TEST(last_index_of_longer_needle) {
    ASSERT_EQ_INT(simple_last_index_of("hi", "longer_string"), -1);
}

/* ================================================================
 * simple_replace tests
 * ================================================================ */

TEST(replace_basic) {
    char* s = simple_replace("hello world", "world", "there");
    ASSERT_EQ_STR(s, "hello there");
    free(s);
}

TEST(replace_multiple) {
    char* s = simple_replace("aabbaa", "aa", "x");
    ASSERT_EQ_STR(s, "xbbx");
    free(s);
}

TEST(replace_no_match) {
    char* s = simple_replace("hello", "xyz", "abc");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(replace_null) {
    char* s = simple_replace(NULL, "a", "b");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(replace_null_args) {
    char* s1 = simple_replace("abc", NULL, "x");
    ASSERT_EQ_STR(s1, "abc");
    free(s1);

    char* s2 = simple_replace("abc", "a", NULL);
    ASSERT_EQ_STR(s2, "abc");
    free(s2);

    char* s3 = simple_replace("abc", "", "x");
    ASSERT_EQ_STR(s3, "abc");
    free(s3);
}

TEST(replace_grow) {
    /* Replacement larger than original */
    char* s = simple_replace("a b c", " ", "---");
    ASSERT_EQ_STR(s, "a---b---c");
    free(s);
}

TEST(replace_shrink) {
    /* Replacement smaller than original */
    char* s = simple_replace("hello world hello", "hello", "hi");
    ASSERT_EQ_STR(s, "hi world hi");
    free(s);
}

/* ================================================================
 * SimpleStringArray tests
 * ================================================================ */

TEST(string_array_new) {
    SimpleStringArray arr = simple_new_string_array();
    ASSERT_EQ_INT(arr.len, 0);
    ASSERT(arr.cap >= 16);
    free(arr.items);
}

TEST(string_array_push_pop) {
    SimpleStringArray arr = simple_new_string_array();
    simple_string_push(&arr, "hello");
    simple_string_push(&arr, "world");
    ASSERT_EQ_INT(arr.len, 2);
    ASSERT_EQ_STR(arr.items[0], "hello");
    ASSERT_EQ_STR(arr.items[1], "world");

    const char* popped = simple_string_pop(&arr);
    ASSERT_EQ_STR(popped, "world");
    ASSERT_EQ_INT(arr.len, 1);

    popped = simple_string_pop(&arr);
    ASSERT_EQ_STR(popped, "hello");
    ASSERT_EQ_INT(arr.len, 0);

    /* Pop from empty */
    popped = simple_string_pop(&arr);
    ASSERT_EQ_STR(popped, "");

    free((void*)arr.items[0]); /* hello */
    free((void*)arr.items[1]); /* world */
    free(arr.items);
}

TEST(string_array_push_null) {
    SimpleStringArray arr = simple_new_string_array();
    simple_string_push(&arr, NULL);
    ASSERT_EQ_INT(arr.len, 1);
    ASSERT_EQ_STR(arr.items[0], "");
    free((void*)arr.items[0]);
    free(arr.items);
}

TEST(string_array_grow) {
    SimpleStringArray arr = simple_new_string_array();
    for (int i = 0; i < 100; i++) {
        char buf[32];
        snprintf(buf, sizeof(buf), "item_%d", i);
        simple_string_push(&arr, buf);
    }
    ASSERT_EQ_INT(arr.len, 100);
    ASSERT_EQ_STR(arr.items[0], "item_0");
    ASSERT_EQ_STR(arr.items[99], "item_99");

    for (int i = 0; i < 100; i++) free((void*)arr.items[i]);
    free(arr.items);
}

/* ================================================================
 * simple_string_join tests
 * ================================================================ */

TEST(string_join_basic) {
    SimpleStringArray arr = simple_new_string_array();
    simple_string_push(&arr, "hello");
    simple_string_push(&arr, "world");
    char* result = simple_string_join(&arr, " ");
    ASSERT_EQ_STR(result, "hello world");
    free(result);
    free((void*)arr.items[0]);
    free((void*)arr.items[1]);
    free(arr.items);
}

TEST(string_join_empty) {
    SimpleStringArray arr = simple_new_string_array();
    char* result = simple_string_join(&arr, ",");
    ASSERT_EQ_STR(result, "");
    free(result);
    free(arr.items);
}

TEST(string_join_single) {
    SimpleStringArray arr = simple_new_string_array();
    simple_string_push(&arr, "only");
    char* result = simple_string_join(&arr, ",");
    ASSERT_EQ_STR(result, "only");
    free(result);
    free((void*)arr.items[0]);
    free(arr.items);
}

TEST(string_join_multi_char_delim) {
    SimpleStringArray arr = simple_new_string_array();
    simple_string_push(&arr, "a");
    simple_string_push(&arr, "b");
    simple_string_push(&arr, "c");
    char* result = simple_string_join(&arr, " | ");
    ASSERT_EQ_STR(result, "a | b | c");
    free(result);
    for (int i = 0; i < 3; i++) free((void*)arr.items[i]);
    free(arr.items);
}

/* ================================================================
 * simple_split tests
 * ================================================================ */

TEST(split_basic) {
    SimpleStringArray arr = simple_split("hello world foo", " ");
    ASSERT_EQ_INT(arr.len, 3);
    ASSERT_EQ_STR(arr.items[0], "hello");
    ASSERT_EQ_STR(arr.items[1], "world");
    ASSERT_EQ_STR(arr.items[2], "foo");
    for (int i = 0; i < arr.len; i++) free((void*)arr.items[i]);
    free(arr.items);
}

TEST(split_null) {
    SimpleStringArray arr = simple_split(NULL, ",");
    ASSERT_EQ_INT(arr.len, 0);
    free(arr.items);
}

TEST(split_no_delim) {
    SimpleStringArray arr = simple_split("hello", NULL);
    ASSERT_EQ_INT(arr.len, 1);
    ASSERT_EQ_STR(arr.items[0], "hello");
    free((void*)arr.items[0]);
    free(arr.items);
}

TEST(split_empty_delim) {
    SimpleStringArray arr = simple_split("hello", "");
    ASSERT_EQ_INT(arr.len, 1);
    ASSERT_EQ_STR(arr.items[0], "hello");
    free((void*)arr.items[0]);
    free(arr.items);
}

TEST(split_multi_char_delim) {
    SimpleStringArray arr = simple_split("a::b::c", "::");
    ASSERT_EQ_INT(arr.len, 3);
    ASSERT_EQ_STR(arr.items[0], "a");
    ASSERT_EQ_STR(arr.items[1], "b");
    ASSERT_EQ_STR(arr.items[2], "c");
    for (int i = 0; i < arr.len; i++) free((void*)arr.items[i]);
    free(arr.items);
}

TEST(split_trailing_delim) {
    SimpleStringArray arr = simple_split("a,b,", ",");
    ASSERT_EQ_INT(arr.len, 3);
    ASSERT_EQ_STR(arr.items[0], "a");
    ASSERT_EQ_STR(arr.items[1], "b");
    ASSERT_EQ_STR(arr.items[2], "");
    for (int i = 0; i < arr.len; i++) free((void*)arr.items[i]);
    free(arr.items);
}

/* ================================================================
 * simple_str_concat tests
 * ================================================================ */

TEST(str_concat_basic) {
    char* s = simple_str_concat("hello", " world");
    ASSERT_EQ_STR(s, "hello world");
    free(s);
}

TEST(str_concat_null) {
    char* s1 = simple_str_concat(NULL, "abc");
    ASSERT_EQ_STR(s1, "abc");
    free(s1);

    char* s2 = simple_str_concat("abc", NULL);
    ASSERT_EQ_STR(s2, "abc");
    free(s2);

    char* s3 = simple_str_concat(NULL, NULL);
    ASSERT_EQ_STR(s3, "");
    free(s3);
}

/* ================================================================
 * simple_char_at tests
 * ================================================================ */

TEST(char_at_basic) {
    char* c = simple_char_at("hello", 0);
    ASSERT_EQ_STR(c, "h");
    free(c);

    char* last = simple_char_at("hello", 4);
    ASSERT_EQ_STR(last, "o");
    free(last);
}

TEST(char_at_negative) {
    char* c = simple_char_at("hello", -1);
    ASSERT_EQ_STR(c, "o");
    free(c);

    char* c2 = simple_char_at("hello", -5);
    ASSERT_EQ_STR(c2, "h");
    free(c2);
}

TEST(char_at_oob) {
    char* c = simple_char_at("hi", 5);
    ASSERT_EQ_STR(c, "");
    free(c);

    char* c2 = simple_char_at("hi", -5);
    ASSERT_EQ_STR(c2, "");
    free(c2);
}

TEST(char_at_null) {
    char* c = simple_char_at(NULL, 0);
    ASSERT_EQ_STR(c, "");
    free(c);
}

/* ================================================================
 * File I/O tests
 * ================================================================ */

TEST(file_write_read) {
    const char* path = "/tmp/c_runtime_test_file.txt";
    ASSERT(simple_file_write(path, "test content"));
    ASSERT(simple_file_exists(path));
    char* content = simple_file_read(path);
    ASSERT_EQ_STR(content, "test content");
    free(content);
    remove(path);
}

TEST(file_read_nonexistent) {
    char* content = simple_file_read("/tmp/c_runtime_nonexistent_12345.txt");
    ASSERT_EQ_STR(content, "");
    free(content);
}

TEST(file_not_exists) {
    ASSERT(!simple_file_exists("/tmp/c_runtime_nonexistent_12345.txt"));
}

TEST(file_write_null_content) {
    const char* path = "/tmp/c_runtime_null_write.txt";
    ASSERT(simple_file_write(path, NULL));
    char* content = simple_file_read(path);
    ASSERT_EQ_STR(content, "");
    free(content);
    remove(path);
}

/* ================================================================
 * Branch Coverage: trim \r and file write invalid path
 * ================================================================ */

TEST(trim_trailing_cr_only) {
    char* s = simple_trim("hello\r");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(trim_leading_cr) {
    char* s = simple_trim("\rhello");
    ASSERT_EQ_STR(s, "hello");
    free(s);
}

TEST(trim_only_cr) {
    char* s = simple_trim("\r\r\r");
    ASSERT_EQ_STR(s, "");
    free(s);
}

TEST(file_write_invalid_path) {
    ASSERT(!simple_file_write("/nonexistent_dir_12345/file.txt", "test"));
}

/* ================================================================
 * simple_shell tests
 * ================================================================ */

TEST(shell_basic) {
    ASSERT_EQ_INT(simple_shell("true"), 0);
}

/* ================================================================
 * simple_format_long / simple_format_str tests
 * ================================================================ */

TEST(format_long_basic) {
    char* s = simple_format_long("count: ", 42, " items");
    ASSERT_EQ_STR(s, "count: 42 items");
    free(s);
}

TEST(format_long_null) {
    char* s = simple_format_long(NULL, 5, NULL);
    ASSERT_EQ_STR(s, "5");
    free(s);
}

TEST(format_str_basic) {
    char* s = simple_format_str("hello ", "world", "!");
    ASSERT_EQ_STR(s, "hello world!");
    free(s);
}

TEST(format_str_null) {
    char* s = simple_format_str(NULL, NULL, NULL);
    ASSERT_EQ_STR(s, "");
    free(s);
}

/* ================================================================
 * simple_int_to_str tests
 * ================================================================ */

TEST(int_to_str_basic) {
    char* s = simple_int_to_str(42);
    ASSERT_EQ_STR(s, "42");
    free(s);
}

TEST(int_to_str_negative) {
    char* s = simple_int_to_str(-123);
    ASSERT_EQ_STR(s, "-123");
    free(s);
}

TEST(int_to_str_zero) {
    char* s = simple_int_to_str(0);
    ASSERT_EQ_STR(s, "0");
    free(s);
}

/* ================================================================
 * SimpleIntArray tests
 * ================================================================ */

TEST(int_array_new) {
    SimpleIntArray arr = simple_new_int_array();
    ASSERT_EQ_INT(arr.len, 0);
    ASSERT(arr.cap >= 16);
    free(arr.items);
}

TEST(int_array_push_pop) {
    SimpleIntArray arr = simple_new_int_array();
    simple_int_push(&arr, 10);
    simple_int_push(&arr, 20);
    simple_int_push(&arr, 30);
    ASSERT_EQ_INT(arr.len, 3);
    ASSERT_EQ_INT(arr.items[0], 10);
    ASSERT_EQ_INT(arr.items[1], 20);
    ASSERT_EQ_INT(arr.items[2], 30);

    long long popped = simple_int_pop(&arr);
    ASSERT_EQ_INT(popped, 30);
    ASSERT_EQ_INT(arr.len, 2);

    popped = simple_int_pop(&arr);
    ASSERT_EQ_INT(popped, 20);
    ASSERT_EQ_INT(arr.len, 1);

    /* Pop from single element */
    popped = simple_int_pop(&arr);
    ASSERT_EQ_INT(popped, 10);
    ASSERT_EQ_INT(arr.len, 0);

    /* Pop from empty */
    popped = simple_int_pop(&arr);
    ASSERT_EQ_INT(popped, 0);

    free(arr.items);
}

TEST(int_array_grow) {
    SimpleIntArray arr = simple_new_int_array();
    for (long long i = 0; i < 100; i++) {
        simple_int_push(&arr, i * 10);
    }
    ASSERT_EQ_INT(arr.len, 100);
    ASSERT_EQ_INT(arr.items[0], 0);
    ASSERT_EQ_INT(arr.items[50], 500);
    ASSERT_EQ_INT(arr.items[99], 990);
    free(arr.items);
}

/* ================================================================
 * SimpleStringArrayArray tests
 * ================================================================ */

TEST(string_array_array_new) {
    SimpleStringArrayArray arr = simple_new_string_array_array();
    ASSERT_EQ_INT(arr.len, 0);
    ASSERT(arr.cap >= 16);
    free(arr.items);
}

TEST(string_array_array_push) {
    SimpleStringArrayArray arr = simple_new_string_array_array();

    SimpleStringArray sub1 = simple_new_string_array();
    simple_string_push(&sub1, "a");
    simple_string_push(&sub1, "b");

    SimpleStringArray sub2 = simple_new_string_array();
    simple_string_push(&sub2, "x");
    simple_string_push(&sub2, "y");

    simple_string_array_push(&arr, sub1);
    simple_string_array_push(&arr, sub2);

    ASSERT_EQ_INT(arr.len, 2);
    ASSERT_EQ_INT(arr.items[0].len, 2);
    ASSERT_EQ_STR(arr.items[0].items[0], "a");
    ASSERT_EQ_STR(arr.items[0].items[1], "b");
    ASSERT_EQ_INT(arr.items[1].len, 2);
    ASSERT_EQ_STR(arr.items[1].items[0], "x");
    ASSERT_EQ_STR(arr.items[1].items[1], "y");

    /* Cleanup */
    for (int i = 0; i < arr.len; i++) {
        for (int j = 0; j < arr.items[i].len; j++) {
            free((void*)arr.items[i].items[j]);
        }
        free(arr.items[i].items);
    }
    free(arr.items);
}

/* ================================================================
 * SimpleIntArrayArray tests
 * ================================================================ */

TEST(int_array_array_new) {
    SimpleIntArrayArray arr = simple_new_int_array_array();
    ASSERT_EQ_INT(arr.len, 0);
    ASSERT(arr.cap >= 16);
    free(arr.items);
}

TEST(int_array_array_push) {
    SimpleIntArrayArray arr = simple_new_int_array_array();

    SimpleIntArray sub1 = simple_new_int_array();
    simple_int_push(&sub1, 1);
    simple_int_push(&sub1, 2);
    simple_int_push(&sub1, 3);

    SimpleIntArray sub2 = simple_new_int_array();
    simple_int_push(&sub2, 10);
    simple_int_push(&sub2, 20);

    simple_int_array_push(&arr, sub1);
    simple_int_array_push(&arr, sub2);

    ASSERT_EQ_INT(arr.len, 2);
    ASSERT_EQ_INT(arr.items[0].len, 3);
    ASSERT_EQ_INT(arr.items[0].items[0], 1);
    ASSERT_EQ_INT(arr.items[0].items[1], 2);
    ASSERT_EQ_INT(arr.items[0].items[2], 3);
    ASSERT_EQ_INT(arr.items[1].len, 2);
    ASSERT_EQ_INT(arr.items[1].items[0], 10);
    ASSERT_EQ_INT(arr.items[1].items[1], 20);

    /* Cleanup */
    for (int i = 0; i < arr.len; i++) {
        free(arr.items[i].items);
    }
    free(arr.items);
}

/* ================================================================
 * SimpleDict tests
 * ================================================================ */

TEST(dict_new) {
    SimpleDict* d = simple_dict_new();
    ASSERT(d != NULL);
    ASSERT_EQ_INT(simple_dict_len(d), 0);
    free(d->entries);
    free(d);
}

TEST(dict_set_get_int) {
    SimpleDict* d = simple_dict_new();
    simple_dict_set_int(d, "age", 42);
    simple_dict_set_int(d, "count", 100);

    ASSERT_EQ_INT(simple_dict_get_int(d, "age"), 42);
    ASSERT_EQ_INT(simple_dict_get_int(d, "count"), 100);
    ASSERT_EQ_INT(simple_dict_len(d), 2);

    /* Overwrite */
    simple_dict_set_int(d, "age", 43);
    ASSERT_EQ_INT(simple_dict_get_int(d, "age"), 43);
    ASSERT_EQ_INT(simple_dict_len(d), 2);

    /* Cleanup */
    for (int i = 0; i < d->len; i++) free((void*)d->entries[i].key);
    free(d->entries);
    free(d);
}

TEST(dict_set_get_str) {
    SimpleDict* d = simple_dict_new();
    simple_dict_set_str(d, "name", "Alice");
    simple_dict_set_str(d, "city", "Boston");

    ASSERT_EQ_STR(simple_dict_get(d, "name"), "Alice");
    ASSERT_EQ_STR(simple_dict_get(d, "city"), "Boston");
    ASSERT_EQ_INT(simple_dict_len(d), 2);

    /* Overwrite */
    simple_dict_set_str(d, "name", "Bob");
    ASSERT_EQ_STR(simple_dict_get(d, "name"), "Bob");
    ASSERT_EQ_INT(simple_dict_len(d), 2);

    /* Cleanup */
    for (int i = 0; i < d->len; i++) {
        free((void*)d->entries[i].key);
        if (d->entries[i].type_tag == SIMPLE_DICT_TYPE_STR) {
            free((void*)d->entries[i].value.str_val);
        }
    }
    free(d->entries);
    free(d);
}

TEST(dict_set_get_ptr) {
    SimpleDict* d = simple_dict_new();
    int x = 42;
    int y = 100;
    simple_dict_set_ptr(d, "ptr1", &x);
    simple_dict_set_ptr(d, "ptr2", &y);

    ASSERT(simple_dict_get_ptr(d, "ptr1") == &x);
    ASSERT(simple_dict_get_ptr(d, "ptr2") == &y);
    ASSERT_EQ_INT(simple_dict_len(d), 2);

    /* Cleanup */
    for (int i = 0; i < d->len; i++) free((void*)d->entries[i].key);
    free(d->entries);
    free(d);
}

TEST(dict_contains) {
    SimpleDict* d = simple_dict_new();
    simple_dict_set_int(d, "x", 10);

    ASSERT(simple_dict_contains(d, "x"));
    ASSERT(!simple_dict_contains(d, "y"));

    /* Cleanup */
    free((void*)d->entries[0].key);
    free(d->entries);
    free(d);
}

TEST(dict_keys) {
    SimpleDict* d = simple_dict_new();
    simple_dict_set_int(d, "alpha", 1);
    simple_dict_set_int(d, "beta", 2);
    simple_dict_set_int(d, "gamma", 3);

    SimpleStringArray keys = simple_dict_keys(d);
    ASSERT_EQ_INT(keys.len, 3);
    ASSERT_EQ_STR(keys.items[0], "alpha");
    ASSERT_EQ_STR(keys.items[1], "beta");
    ASSERT_EQ_STR(keys.items[2], "gamma");

    /* Cleanup */
    for (int i = 0; i < keys.len; i++) free((void*)keys.items[i]);
    free(keys.items);
    for (int i = 0; i < d->len; i++) free((void*)d->entries[i].key);
    free(d->entries);
    free(d);
}

TEST(dict_remove) {
    SimpleDict* d = simple_dict_new();
    simple_dict_set_int(d, "a", 1);
    simple_dict_set_int(d, "b", 2);
    simple_dict_set_int(d, "c", 3);

    ASSERT_EQ_INT(simple_dict_len(d), 3);
    simple_dict_remove(d, "b");
    ASSERT_EQ_INT(simple_dict_len(d), 2);
    ASSERT(simple_dict_contains(d, "a"));
    ASSERT(!simple_dict_contains(d, "b"));
    ASSERT(simple_dict_contains(d, "c"));

    /* Remove non-existent */
    simple_dict_remove(d, "xyz");
    ASSERT_EQ_INT(simple_dict_len(d), 2);

    /* Cleanup */
    for (int i = 0; i < d->len; i++) free((void*)d->entries[i].key);
    free(d->entries);
    free(d);
}

TEST(dict_get_int_converts_from_str) {
    SimpleDict* d = simple_dict_new();
    simple_dict_set_int(d, "num", 42);

    /* Get as string (converts int to string) */
    const char* s = simple_dict_get(d, "num");
    ASSERT_EQ_STR(s, "42");
    free((void*)s);

    /* Cleanup */
    free((void*)d->entries[0].key);
    free(d->entries);
    free(d);
}

TEST(dict_null_operations) {
    ASSERT_EQ_INT(simple_dict_len(NULL), 0);
    ASSERT_EQ_INT(simple_dict_get_int(NULL, "key"), 0);
    ASSERT(simple_dict_get_ptr(NULL, "key") == NULL);
    ASSERT(simple_dict_get(NULL, "key") == NULL);

    SimpleDict* d = simple_dict_new();
    simple_dict_set_int(d, NULL, 42);
    simple_dict_set_str(d, NULL, "test");
    simple_dict_set_ptr(d, NULL, NULL);
    ASSERT_EQ_INT(simple_dict_len(d), 0);

    simple_dict_remove(d, NULL);
    simple_dict_remove(NULL, "key");

    free(d->entries);
    free(d);
}

TEST(dict_grow) {
    SimpleDict* d = simple_dict_new();
    for (int i = 0; i < 100; i++) {
        char key[32];
        snprintf(key, sizeof(key), "key_%d", i);
        simple_dict_set_int(d, key, i * 10);
    }
    ASSERT_EQ_INT(simple_dict_len(d), 100);
    ASSERT_EQ_INT(simple_dict_get_int(d, "key_0"), 0);
    ASSERT_EQ_INT(simple_dict_get_int(d, "key_50"), 500);
    ASSERT_EQ_INT(simple_dict_get_int(d, "key_99"), 990);

    /* Cleanup */
    for (int i = 0; i < d->len; i++) free((void*)d->entries[i].key);
    free(d->entries);
    free(d);
}

/* ================================================================
 * SimpleOption tests
 * ================================================================ */

TEST(option_none) {
    SimpleOption o = simple_none();
    ASSERT(!simple_option_has(o));
    ASSERT_EQ_INT(o.has_value, 0);
}

TEST(option_some_int) {
    SimpleOption o = simple_some_int(42);
    ASSERT(simple_option_has(o));
    ASSERT_EQ_INT(simple_option_unwrap_int(o), 42);
}

TEST(option_some_str) {
    SimpleOption o = simple_some_str("hello");
    ASSERT(simple_option_has(o));
    ASSERT_EQ_STR(simple_option_unwrap_str(o), "hello");
    free((void*)o.str_val);
}

TEST(option_some_str_null) {
    SimpleOption o = simple_some_str(NULL);
    ASSERT(simple_option_has(o));
    ASSERT_EQ_STR(simple_option_unwrap_str(o), "");
    free((void*)o.str_val);
}

TEST(option_some_ptr) {
    int x = 123;
    SimpleOption o = simple_some_ptr(&x);
    ASSERT(simple_option_has(o));
    ASSERT(simple_option_unwrap_ptr(o) == &x);
}

TEST(option_unwrap_none_str) {
    SimpleOption o = simple_none();
    ASSERT_EQ_STR(simple_option_unwrap_str(o), "");
}

TEST(option_unwrap_none_ptr) {
    SimpleOption o = simple_none();
    ASSERT(simple_option_unwrap_ptr(o) == NULL);
}

TEST(option_unwrap_wrong_type) {
    SimpleOption o = simple_some_int(42);
    /* Unwrapping int option as string should return empty */
    ASSERT_EQ_STR(simple_option_unwrap_str(o), "");
    /* Unwrapping int option as ptr should return NULL */
    ASSERT(simple_option_unwrap_ptr(o) == NULL);
}

/* ================================================================
 * SimpleResult tests
 * ================================================================ */

TEST(result_ok_int) {
    SimpleResult r = simple_result_ok_int(42);
    ASSERT(r.is_ok);
    ASSERT_EQ_INT(r.ok_int, 42);
}

TEST(result_ok_str) {
    SimpleResult r = simple_result_ok_str("success");
    ASSERT(r.is_ok);
    ASSERT_EQ_STR(r.ok_str, "success");
    free((void*)r.ok_str);
}

TEST(result_ok_str_null) {
    SimpleResult r = simple_result_ok_str(NULL);
    ASSERT(r.is_ok);
    ASSERT_EQ_STR(r.ok_str, "");
    free((void*)r.ok_str);
}

TEST(result_err_str) {
    SimpleResult r = simple_result_err_str("error message");
    ASSERT(!r.is_ok);
    ASSERT_EQ_STR(r.err_str, "error message");
    free((void*)r.err_str);
}

TEST(result_err_str_null) {
    SimpleResult r = simple_result_err_str(NULL);
    ASSERT(!r.is_ok);
    ASSERT_EQ_STR(r.err_str, "");
    free((void*)r.err_str);
}

/* ================================================================
 * Main
 * ================================================================ */

int main(void) {
    printf("=== c_runtime.c Test Suite ===\n\n");

    printf("--- String Operations ---\n");
    RUN(strlen_basic);
    RUN(substring_basic);
    RUN(substring_middle);
    RUN(substring_null);
    RUN(substring_clamp);
    RUN(substring_empty_range);
    RUN(contains_basic);
    RUN(contains_null);
    RUN(starts_with_basic);
    RUN(starts_with_null);
    RUN(ends_with_basic);
    RUN(ends_with_null);
    RUN(ends_with_longer_suffix);
    RUN(trim_basic);
    RUN(trim_tabs_newlines);
    RUN(trim_null);
    RUN(trim_empty);
    RUN(trim_all_whitespace);
    RUN(trim_no_whitespace);
    RUN(index_of_basic);
    RUN(index_of_null);
    RUN(last_index_of_basic);
    RUN(last_index_of_null);
    RUN(last_index_of_longer_needle);
    RUN(replace_basic);
    RUN(replace_multiple);
    RUN(replace_no_match);
    RUN(replace_null);
    RUN(replace_null_args);
    RUN(replace_grow);
    RUN(replace_shrink);

    printf("\n--- String Array ---\n");
    RUN(string_array_new);
    RUN(string_array_push_pop);
    RUN(string_array_push_null);
    RUN(string_array_grow);

    printf("\n--- String Join ---\n");
    RUN(string_join_basic);
    RUN(string_join_empty);
    RUN(string_join_single);
    RUN(string_join_multi_char_delim);

    printf("\n--- String Split ---\n");
    RUN(split_basic);
    RUN(split_null);
    RUN(split_no_delim);
    RUN(split_empty_delim);
    RUN(split_multi_char_delim);
    RUN(split_trailing_delim);

    printf("\n--- String Helpers ---\n");
    RUN(str_concat_basic);
    RUN(str_concat_null);
    RUN(char_at_basic);
    RUN(char_at_negative);
    RUN(char_at_oob);
    RUN(char_at_null);

    printf("\n--- File I/O ---\n");
    RUN(file_write_read);
    RUN(file_read_nonexistent);
    RUN(file_not_exists);
    RUN(file_write_null_content);

    printf("\n--- Branch Coverage ---\n");
    RUN(trim_trailing_cr_only);
    RUN(trim_leading_cr);
    RUN(trim_only_cr);
    RUN(file_write_invalid_path);

    printf("\n--- Shell ---\n");
    RUN(shell_basic);

    printf("\n--- Formatting ---\n");
    RUN(format_long_basic);
    RUN(format_long_null);
    RUN(format_str_basic);
    RUN(format_str_null);

    printf("\n--- Int to String ---\n");
    RUN(int_to_str_basic);
    RUN(int_to_str_negative);
    RUN(int_to_str_zero);

    printf("\n--- Int Array ---\n");
    RUN(int_array_new);
    RUN(int_array_push_pop);
    RUN(int_array_grow);

    printf("\n--- String Array Array ---\n");
    RUN(string_array_array_new);
    RUN(string_array_array_push);

    printf("\n--- Int Array Array ---\n");
    RUN(int_array_array_new);
    RUN(int_array_array_push);

    printf("\n--- Dictionary ---\n");
    RUN(dict_new);
    RUN(dict_set_get_int);
    RUN(dict_set_get_str);
    RUN(dict_set_get_ptr);
    RUN(dict_contains);
    RUN(dict_keys);
    RUN(dict_remove);
    RUN(dict_get_int_converts_from_str);
    RUN(dict_null_operations);
    RUN(dict_grow);

    printf("\n--- Option Type ---\n");
    RUN(option_none);
    RUN(option_some_int);
    RUN(option_some_str);
    RUN(option_some_str_null);
    RUN(option_some_ptr);
    RUN(option_unwrap_none_str);
    RUN(option_unwrap_none_ptr);
    RUN(option_unwrap_wrong_type);

    printf("\n--- Result Type ---\n");
    RUN(result_ok_int);
    RUN(result_ok_str);
    RUN(result_ok_str_null);
    RUN(result_err_str);
    RUN(result_err_str_null);

    printf("\n=== All %d tests passed ===\n", tests_run);
    return 0;
}
