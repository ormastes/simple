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

    printf("\n=== All %d tests passed ===\n", tests_run);
    return 0;
}
