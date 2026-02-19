/*
 * seed_branch_test.cpp -- Intensive Branch Coverage Tests for seed.cpp
 *
 * Targets uncovered branches in the seed compiler's code generation.
 * Uses the same test harness as seed_test.cpp.
 *
 * Build (Windows):
 *   cl /std:c++20 /EHsc /Fe:seed_branch_test.exe seed_branch_test.cpp
 *   set SEED_CPP=path\to\seed_cpp.exe
 *   seed_branch_test.exe
 *
 * Build (Linux/macOS):
 *   c++ -std=c++20 -o /tmp/seed_branch_test seed/seed_branch_test.cpp
 *   SEED_CPP=/tmp/seed_cpp /tmp/seed_branch_test
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

#ifdef _WIN32
#define popen _popen
#define pclose _pclose
#endif

static int tests_run = 0;
static int tests_passed = 0;
static const char* seed_binary = nullptr;

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

#define ASSERT_CONTAINS(haystack, needle) do { \
    if (strstr((haystack), (needle)) == nullptr) { \
        printf(" FAIL\n    output missing: \"%s\"\n    %s:%d\n", (needle), __FILE__, __LINE__); \
        fprintf(stderr, "  Full output:\n%s\n", (haystack)); \
        exit(1); \
    } \
} while(0)

#define ASSERT_NOT_CONTAINS(haystack, needle) do { \
    if (strstr((haystack), (needle)) != nullptr) { \
        printf(" FAIL\n    output should not contain: \"%s\"\n    %s:%d\n", (needle), __FILE__, __LINE__); \
        exit(1); \
    } \
} while(0)

/* Write content to a temp .spl file, compile with seed, return output */
static std::string compile_spl(const char* content) {
#ifdef _WIN32
    const char* path = "C:\\Windows\\Temp\\_seed_branch_test_input.spl";
#else
    const char* path = "/tmp/_seed_branch_test_input.spl";
#endif
    FILE* f = fopen(path, "w");
    if (!f) { perror("fopen"); exit(1); }
    fputs(content, f);
    fclose(f);

    char cmd[1024];
#ifdef _WIN32
    snprintf(cmd, sizeof(cmd), "%s %s 2>NUL", seed_binary, path);
#else
    snprintf(cmd, sizeof(cmd), "%s %s 2>/dev/null", seed_binary, path);
#endif
    FILE* p = popen(cmd, "r");
    if (!p) { perror("popen"); exit(1); }

    std::string result;
    char buf[4096];
    while (fgets(buf, sizeof(buf), p)) result += buf;
    pclose(p);
    return result;
}


/* ================================================================
 * 1. String Interpolation Edge Cases
 * ================================================================ */

TEST(interp_multiple_adjacent) {
    /* Two interpolations with no text between: "{a}{b}" */
    auto out = compile_spl(
        "fn test(a: i64, b: i64) -> text:\n"
        "    return \"{a}{b}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

TEST(interp_with_expression) {
    /* Interpolation with a binary expression: "{x + 1}" */
    auto out = compile_spl(
        "fn test(x: i64) -> text:\n"
        "    return \"result: {x + 1}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

TEST(interp_trailing_text) {
    /* Interpolation with text after: "{x} items" */
    auto out = compile_spl(
        "fn test(x: i64) -> text:\n"
        "    return \"{x} items\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "\" items\"");
}

TEST(interp_text_var_no_conversion) {
    /* text interpolation: no spl_i64_to_str needed */
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return \"hello {s} world\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_NOT_CONTAINS(out.c_str(), "spl_i64_to_str(s)");
}

TEST(interp_mixed_types) {
    /* Mix text and int interpolations */
    auto out = compile_spl(
        "fn test(n: text, v: i64) -> text:\n"
        "    return \"{n}={v}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

TEST(interp_string_literal_expr) {
    /* Interpolation with a string literal as expr */
    auto out = compile_spl(
        "fn test() -> text:\n"
        "    val s: text = \"inner\"\n"
        "    return \"outer:{s}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

TEST(interp_three_segments) {
    /* Three segments: literal + interp + literal + interp + literal */
    auto out = compile_spl(
        "fn test(a: i64, b: i64) -> text:\n"
        "    return \"x={a},y={b}.\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "\"x=\"");
}

/* ================================================================
 * 2. Operator Translation Branches
 * ================================================================ */

TEST(op_and_translation) {
    auto out = compile_spl(
        "fn test(a: bool, b: bool) -> bool:\n"
        "    return a and b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "&&");
}

TEST(op_or_translation) {
    auto out = compile_spl(
        "fn test(a: bool, b: bool) -> bool:\n"
        "    return a or b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "||");
}

TEST(op_not_translation) {
    auto out = compile_spl(
        "fn test(a: bool) -> bool:\n"
        "    return not a\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!(");
}

TEST(op_nil_coalescing_option) {
    /* ?? with Option type: use .has_value and .value */
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    var opt: i64? = 5\n"
        "    return opt ?? 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
    ASSERT_CONTAINS(out.c_str(), ".value");
}

TEST(op_nil_coalescing_plain) {
    /* ?? with non-option: ternary fallback */
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    return x ?? 0\n"
    );
    /* Non-option gets ternary */
    ASSERT_CONTAINS(out.c_str(), "?");
    ASSERT_CONTAINS(out.c_str(), ":");
}

TEST(op_string_plus_concatenation) {
    /* + with text types triggers spl_str_concat */
    auto out = compile_spl(
        "fn test(a: text, b: text) -> text:\n"
        "    return a + b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

TEST(op_nil_eq_text) {
    /* nil == text_var -> NULL comparison */
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s == nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "== NULL");
}

TEST(op_nil_ne_text) {
    /* nil != text_var */
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s != nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!= NULL");
}

TEST(op_nil_eq_int) {
    /* nil == i64 -> -1 comparison */
    auto out = compile_spl(
        "fn test(x: i64) -> bool:\n"
        "    return x == nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "== -1");
}

TEST(op_nil_ne_int) {
    /* nil != i64 */
    auto out = compile_spl(
        "fn test(x: i64) -> bool:\n"
        "    return x != nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!= -1");
}

TEST(op_nil_left_side_eq_option) {
    /* nil == option -> !has_value */
    auto out = compile_spl(
        "fn test() -> bool:\n"
        "    var x: i64? = 5\n"
        "    return nil == x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!x.has_value");
}

TEST(op_nil_left_side_ne_option) {
    /* nil != option -> has_value */
    auto out = compile_spl(
        "fn test() -> bool:\n"
        "    var x: i64? = 5\n"
        "    return nil != x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x.has_value");
}

/* ================================================================
 * 3. Method Call Branches
 * ================================================================ */

TEST(method_len_on_text) {
    auto out = compile_spl(
        "fn test(s: text) -> i64:\n"
        "    return s.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_len");
}

TEST(method_len_on_array) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    var a: [i64] = []\n"
        "    return a.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_len");
}

TEST(method_len_on_struct_array) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "fn test() -> i64:\n"
        "    var items: [Item] = []\n"
        "    return items.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".size()");
}

TEST(method_push_on_struct_array) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    items.push(Item(v: 1))\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".push_back(");
}

TEST(method_push_on_nested_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var outer: [[i64]] = []\n"
        "    var inner: [i64] = []\n"
        "    outer.push(inner)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_val(");
}

TEST(method_push_on_text_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = []\n"
        "    arr.push(\"hello\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

TEST(method_push_on_float_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [f64] = []\n"
        "    arr.push(3.14)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_float(");
}

TEST(method_push_on_int_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = []\n"
        "    arr.push(42)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_int(");
}

TEST(method_pop_on_struct_array) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    val last: Item = items.pop()\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".back()");
    ASSERT_CONTAINS(out.c_str(), ".pop_back()");
}

TEST(method_pop_on_int_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2]\n"
        "    val v: i64 = arr.pop()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_pop(");
    ASSERT_CONTAINS(out.c_str(), ".as_int");
}

TEST(method_contains_on_text) {
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s.contains(\"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_contains");
}

TEST(method_starts_with) {
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s.starts_with(\"pre\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_starts_with");
}

TEST(method_ends_with) {
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s.ends_with(\"suf\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_ends_with");
}

TEST(method_index_of) {
    auto out = compile_spl(
        "fn test(s: text) -> i64:\n"
        "    return s.index_of(\"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_of");
}

TEST(method_trim) {
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s.trim()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_trim");
}

TEST(method_replace) {
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s.replace(\"a\", \"b\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_replace");
}

TEST(method_slice_on_text) {
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s.slice(0, 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

/* ================================================================
 * 4. Array Operations
 * ================================================================ */

TEST(array_literal_empty) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new()");
}

TEST(array_literal_with_ints) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [10, 20, 30]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
    ASSERT_CONTAINS(out.c_str(), "spl_int(10)");
    ASSERT_CONTAINS(out.c_str(), "spl_int(30)");
}

TEST(array_literal_with_text) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = [\"a\", \"b\"]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

TEST(array_indexing_int) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    var arr: [i64] = [1, 2]\n"
        "    return arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get(");
    ASSERT_CONTAINS(out.c_str(), ".as_int");
}

TEST(array_indexing_text) {
    auto out = compile_spl(
        "fn test() -> text:\n"
        "    var arr: [text] = [\"a\"]\n"
        "    return arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".as_str");
}

TEST(array_indexing_float) {
    auto out = compile_spl(
        "fn test() -> f64:\n"
        "    var arr: [f64] = []\n"
        "    return arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".as_float");
}

TEST(array_indexing_nested) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [[i64]] = []\n"
        "    val inner: [i64] = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".as_array");
}

TEST(array_indexing_struct) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
        "    val p: Pt = pts[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "pts[0]");
}

TEST(array_set_int) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1]\n"
        "    arr[0] = 99\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set(");
    ASSERT_CONTAINS(out.c_str(), "spl_int(");
}

TEST(array_set_text) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = [\"a\"]\n"
        "    arr[0] = \"b\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set(");
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

TEST(array_set_nested) {
    auto out = compile_spl(
        "fn test():\n"
        "    var outer: [[i64]] = []\n"
        "    var inner: [i64] = []\n"
        "    outer[0] = inner\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set(");
    ASSERT_CONTAINS(out.c_str(), "spl_array_val(");
}

TEST(array_set_struct) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
        "    pts[0] = Pt(x: 1)\n"
    );
    /* Struct array set uses direct indexing */
    ASSERT_CONTAINS(out.c_str(), "pts[0] =");
}

/* ================================================================
 * 5. For Loop Variants
 * ================================================================ */

TEST(for_dotdot_range) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 0; i < 10; i++)");
}

TEST(for_range_one_arg) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(5):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 0; i < 5; i++)");
}

TEST(for_range_two_args) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(3, 8):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 3; i < 8; i++)");
}

TEST(for_in_int_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2]\n"
        "    for x in arr:\n"
        "        print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_len(");
    ASSERT_CONTAINS(out.c_str(), "spl_array_get(");
    ASSERT_CONTAINS(out.c_str(), ".as_int");
}

TEST(for_in_text_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = [\"a\"]\n"
        "    for s in arr:\n"
        "        print s\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char*");
    ASSERT_CONTAINS(out.c_str(), ".as_str");
}

TEST(for_in_float_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [f64] = []\n"
        "    for x in arr:\n"
        "        print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "double");
    ASSERT_CONTAINS(out.c_str(), ".as_float");
}

TEST(for_in_nested_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [[i64]] = []\n"
        "    for inner in arr:\n"
        "        print inner\n"
    );
    ASSERT_CONTAINS(out.c_str(), "SplArray*");
    ASSERT_CONTAINS(out.c_str(), ".as_array");
}

TEST(for_in_struct_array) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
        "    for p in pts:\n"
        "        print p\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".size()");
    ASSERT_CONTAINS(out.c_str(), "Pt p =");
}

TEST(for_in_numeric_expr) {
    /* for i in N where N is a plain number (not a var or function call) */
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 5:\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 0; i < 5; i++)");
}

/* ================================================================
 * 6. Match/Case Branches
 * ================================================================ */

TEST(match_simple_int) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 0:\n"
        "            return 10\n"
        "        case 1:\n"
        "            return 20\n"
        "        case _:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
    ASSERT_CONTAINS(out.c_str(), "case 0:");
    ASSERT_CONTAINS(out.c_str(), "case 1:");
    ASSERT_CONTAINS(out.c_str(), "default:");
}

TEST(match_pipe_separated) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 1 | 2 | 3:\n"
        "            return 100\n"
        "        case _:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case 1:");
    ASSERT_CONTAINS(out.c_str(), "case 2:");
    ASSERT_CONTAINS(out.c_str(), "case 3:");
}

TEST(match_enum_variant) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Green\n"
        "    Blue\n"
        "fn test(c: i64) -> i64:\n"
        "    match c:\n"
        "        case Red:\n"
        "            return 1\n"
        "        case Green:\n"
        "            return 2\n"
        "        case Blue:\n"
        "            return 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case Color_Red:");
    ASSERT_CONTAINS(out.c_str(), "case Color_Green:");
    ASSERT_CONTAINS(out.c_str(), "case Color_Blue:");
}

TEST(match_pipe_with_enum_and_default) {
    auto out = compile_spl(
        "enum Dir:\n"
        "    Up\n"
        "    Down\n"
        "    Left\n"
        "    Right\n"
        "fn test(d: i64) -> i64:\n"
        "    match d:\n"
        "        case Up | Down:\n"
        "            return 1\n"
        "        case Left | Right:\n"
        "            return 2\n"
        "        case _:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case Dir_Up:");
    ASSERT_CONTAINS(out.c_str(), "case Dir_Down:");
    ASSERT_CONTAINS(out.c_str(), "case Dir_Left:");
    ASSERT_CONTAINS(out.c_str(), "case Dir_Right:");
    ASSERT_CONTAINS(out.c_str(), "default:");
}

/* ================================================================
 * 7. Variable Declarations (val/var) Branches
 * ================================================================ */

TEST(val_i64_explicit) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const int64_t x = 42");
}

TEST(var_i64_explicit) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x = 0");
}

TEST(val_text_inferred) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s = \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

TEST(val_bool_inferred) {
    auto out = compile_spl(
        "fn test():\n"
        "    val b = false\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

TEST(val_array_inferred) {
    auto out = compile_spl(
        "fn test():\n"
        "    val arr = [1, 2]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new()");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

TEST(val_struct_inferred) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    val p = Pt(x: 5)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

TEST(var_option_nil_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64 opt = {}");
}

TEST(var_option_value_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64 opt = 42");
}

TEST(val_struct_array) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    val pts: [Pt] = []\n"
    );
    /* Struct array uses std::vector */
    ASSERT_CONTAINS(out.c_str(), "std::vector<Pt>");
}

TEST(var_struct_array_init) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Pt>");
}

/* ================================================================
 * 8. Function Signature Branches
 * ================================================================ */

TEST(fn_multi_params) {
    auto out = compile_spl(
        "fn add(a: i64, b: i64, c: i64) -> i64:\n"
        "    return a + b + c\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t a, int64_t b, int64_t c");
}

TEST(fn_typed_return) {
    auto out = compile_spl(
        "fn greet() -> text:\n"
        "    return \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* greet(");
}

TEST(fn_void_implicit) {
    auto out = compile_spl(
        "fn noop():\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "void noop(");
}

TEST(fn_param_no_type_default_i64) {
    auto out = compile_spl(
        "fn inc(x) -> i64:\n"
        "    return x + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x");
}

TEST(extern_fn_declaration) {
    auto out = compile_spl(
        "extern fn rt_read(path: text) -> text\n"
    );
    ASSERT_CONTAINS(out.c_str(), "extern \"C\"");
    ASSERT_CONTAINS(out.c_str(), "const char* rt_read(");
}

TEST(extern_fn_multiple_params) {
    auto out = compile_spl(
        "extern fn rt_write(path: text, data: text) -> i64\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* path, const char* data");
}

/* ================================================================
 * 9. Implicit Return Branches
 * ================================================================ */

TEST(implicit_return_expr) {
    auto out = compile_spl(
        "fn double(x: i64) -> i64:\n"
        "    x * 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return (x * 2)");
}

TEST(implicit_return_func_call) {
    auto out = compile_spl(
        "fn helper() -> i64:\n"
        "    return 5\n"
        "fn test() -> i64:\n"
        "    helper()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return helper()");
}

TEST(implicit_return_not_for_void) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 42\n"
    );
    /* void fn should not add return */
    ASSERT_NOT_CONTAINS(out.c_str(), "return const");
}

TEST(implicit_return_not_for_assignment) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    var x: i64 = 0\n"
        "    x = 5\n"
    );
    /* Assignment last line should not get return */
    ASSERT_NOT_CONTAINS(out.c_str(), "return x = 5");
}

TEST(implicit_return_not_for_if) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    if true:\n"
        "        return 1\n"
    );
    /* Last stmt is 'if', no return added */
    ASSERT_NOT_CONTAINS(out.c_str(), "return if");
}

/* ================================================================
 * 10. Assignment Operator Branches
 * ================================================================ */

TEST(assign_plus_equals) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    x += 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x += 5");
}

TEST(assign_minus_equals) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 10\n"
        "    x -= 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x -= 3");
}

TEST(assign_array_element) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2]\n"
        "    arr[0] = 99\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set(");
}

TEST(assign_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = 5\n"
        "    opt = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt = {}");
}

TEST(assign_struct_array_clear) {
    /* pool = [] on struct array -> .clear() */
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
        "    pts = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".clear()");
}

/* ================================================================
 * 11. Control Flow: break, continue, return
 * ================================================================ */

TEST(ctrl_break_in_for) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if i == 5:\n"
        "            break\n"
    );
    ASSERT_CONTAINS(out.c_str(), "break;");
}

TEST(ctrl_continue_in_for) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if i == 3:\n"
        "            continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "continue;");
}

TEST(ctrl_return_mid_function) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    if true:\n"
        "        return 42\n"
        "    return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 42");
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

TEST(ctrl_bare_return) {
    auto out = compile_spl(
        "fn test():\n"
        "    return\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return;");
}

TEST(ctrl_return_nil_from_option) {
    auto out = compile_spl(
        "fn find() -> i64?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {};");
}

/* ================================================================
 * 12. Struct Method Branches (self, me, static)
 * ================================================================ */

TEST(struct_method_self_field) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "impl Pt:\n"
        "    fn get_x() -> i64:\n"
        "        return self.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->x");
    ASSERT_CONTAINS(out.c_str(), "const Pt* self");
}

TEST(struct_method_me_mutable) {
    auto out = compile_spl(
        "struct Counter:\n"
        "    n: i64\n"
        "impl Counter:\n"
        "    me inc():\n"
        "        self.n = self.n + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Counter* self");
    ASSERT_CONTAINS(out.c_str(), "self->n =");
}

TEST(struct_method_static_no_self) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "impl Pt:\n"
        "    static fn zero() -> Pt:\n"
        "        return Pt(x: 0)\n"
    );
    /* Static methods don't get self param */
    ASSERT_NOT_CONTAINS(out.c_str(), "Pt* self");
    ASSERT_CONTAINS(out.c_str(), "Pt__zero()");
}

TEST(struct_method_call_from_self) {
    /* Calling method on self should NOT add & */
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn get_v() -> i64:\n"
        "        return self.v\n"
        "    fn doubled() -> i64:\n"
        "        return self.get_v() * 2\n"
    );
    /* self is already a pointer; should use Obj__get_v(self, ...) without & */
    ASSERT_CONTAINS(out.c_str(), "Obj__get_v(self)");
}

/* ================================================================
 * 13. Print Statement Branches
 * ================================================================ */

TEST(print_text_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    print \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println(");
}

TEST(print_int_var) {
    auto out = compile_spl(
        "fn test(x: i64):\n"
        "    print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf(\"%lld\\n\"");
}

TEST(print_text_var) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    print s\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println(s)");
}

TEST(print_interpolated_string) {
    auto out = compile_spl(
        "fn test(x: i64):\n"
        "    print \"val={x}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println(");
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* ================================================================
 * 14. Module-Level Code Branches
 * ================================================================ */

TEST(module_val_const_text) {
    auto out = compile_spl(
        "val NAME: text = \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static const char* NAME = \"hello\"");
}

TEST(module_var_int_const) {
    auto out = compile_spl(
        "var count: i64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t count = 0");
}

TEST(module_var_array) {
    auto out = compile_spl(
        "var items: [i64] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static SplArray* items");
}

TEST(module_var_option) {
    auto out = compile_spl(
        "var opt: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Option_i64 opt = {}");
}

TEST(module_var_struct) {
    auto out = compile_spl(
        "struct Cfg:\n"
        "    v: i64\n"
        "var cfg: Cfg = Cfg(v: 1)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Cfg cfg = {}");
}

TEST(module_var_dynamic_text) {
    auto out = compile_spl(
        "fn get() -> text:\n"
        "    return \"x\"\n"
        "var s: text = get()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static const char* s = \"\"");
    ASSERT_CONTAINS(out.c_str(), "s = get()");
}

TEST(module_var_dynamic_bool) {
    auto out = compile_spl(
        "fn flag() -> bool:\n"
        "    return true\n"
        "var b: bool = flag()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static bool b = false");
    ASSERT_CONTAINS(out.c_str(), "b = flag()");
}

TEST(module_var_dynamic_int) {
    auto out = compile_spl(
        "fn calc() -> i64:\n"
        "    return 42\n"
        "var n: i64 = calc()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t n = 0");
    ASSERT_CONTAINS(out.c_str(), "n = calc()");
}

TEST(module_level_fn_call) {
    auto out = compile_spl(
        "fn init():\n"
        "    pass\n"
        "init()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "__module_init");
    ASSERT_CONTAINS(out.c_str(), "init()");
}

/* ================================================================
 * 15. Type Conversions: simple_type_to_cpp coverage
 * ================================================================ */

TEST(type_i32) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i32 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int32_t x");
}

TEST(type_u8) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: u8 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "uint8_t x");
}

TEST(type_u32) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: u32 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "uint32_t x");
}

TEST(type_u64) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: u64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "uint64_t x");
}

TEST(type_f64) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: f64 = 3.14\n"
    );
    ASSERT_CONTAINS(out.c_str(), "double x");
}

TEST(type_f32) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: f32 = 1.5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "float x");
}

TEST(type_bool) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: bool = true\n"
    );
    ASSERT_CONTAINS(out.c_str(), "bool x");
}

TEST(type_text) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: text = \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* x");
}

TEST(type_option_text) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: text? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
}

TEST(type_option_bool) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: bool? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_bool");
}

TEST(type_option_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: [i64]? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_array");
}

TEST(type_enum_is_i64) {
    auto out = compile_spl(
        "enum Dir:\n"
        "    Up\n"
        "fn test():\n"
        "    val d: Dir = Up\n"
    );
    /* enum type maps to int64_t */
    ASSERT_CONTAINS(out.c_str(), "int64_t d");
}

TEST(type_struct_value) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    val p: Pt = Pt(x: 0)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

TEST(type_struct_array_vector) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Pt>");
}

/* ================================================================
 * 16. Edge Cases: empty/comment
 * ================================================================ */

TEST(empty_file) {
    auto out = compile_spl("");
    ASSERT_CONTAINS(out.c_str(), "int main(");
    ASSERT_CONTAINS(out.c_str(), "__module_init");
}

TEST(comment_only_file) {
    auto out = compile_spl(
        "# just a comment\n"
        "# another comment\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int main(");
}

TEST(empty_fn_body_with_pass) {
    auto out = compile_spl(
        "fn noop():\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "/* pass */");
}

TEST(unit_expr_statement) {
    auto out = compile_spl(
        "fn test():\n"
        "    ()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "/* pass */");
}

/* ================================================================
 * 17. Constructor Calls
 * ================================================================ */

TEST(constructor_named_fields) {
    auto out = compile_spl(
        "struct Rect:\n"
        "    w: i64\n"
        "    h: i64\n"
        "fn test():\n"
        "    val r: Rect = Rect(w: 10, h: 20)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Rect{.w = 10, .h = 20}");
}

TEST(constructor_with_expr) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "    y: i64\n"
        "fn test(a: i64):\n"
        "    val p: Pt = Pt(x: a + 1, y: a * 2)\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".x = (a + 1)");
    ASSERT_CONTAINS(out.c_str(), ".y = (a * 2)");
}

TEST(constructor_with_string_field) {
    auto out = compile_spl(
        "struct Token:\n"
        "    kind: text\n"
        "    value: text\n"
        "fn test():\n"
        "    val t: Token = Token(kind: \"id\", value: \"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".kind = \"id\"");
    ASSERT_CONTAINS(out.c_str(), ".value = \"x\"");
}

/* ================================================================
 * 18. Use/Export Directives (should be skipped)
 * ================================================================ */

TEST(use_directive_skipped) {
    auto out = compile_spl(
        "use std.io\n"
        "fn test():\n"
        "    print \"hello\"\n"
    );
    /* use should not cause errors */
    ASSERT_CONTAINS(out.c_str(), "void test(");
}

TEST(export_directive_skipped) {
    auto out = compile_spl(
        "export test\n"
        "fn test():\n"
        "    print \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "void test(");
}

TEST(import_directive_skipped) {
    auto out = compile_spl(
        "import foo\n"
        "fn test():\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "void test(");
}

TEST(use_inside_function_skipped) {
    auto out = compile_spl(
        "fn test():\n"
        "    use std.io\n"
        "    print \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

/* ================================================================
 * 19. Struct Field Access Edge Cases
 * ================================================================ */

TEST(field_access_struct_array_index) {
    auto out = compile_spl(
        "struct Data:\n"
        "    items: [i64]\n"
        "fn test():\n"
        "    var d: Data = Data(items: [])\n"
        "    val v: i64 = d.items[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get(d.items, 0)");
}

TEST(field_access_struct_text_index) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "fn test():\n"
        "    val d: Info = Info(name: \"hello\")\n"
        "    val c: text = d.name[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_char(d.name, 0)");
}

TEST(field_access_struct_text_slice) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "fn test():\n"
        "    val d: Info = Info(name: \"hello\")\n"
        "    val sub: text = d.name[1:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice(d.name, 1, 3)");
}

TEST(field_access_struct_text_array_element) {
    auto out = compile_spl(
        "struct Data:\n"
        "    names: [text]\n"
        "fn test():\n"
        "    var d: Data = Data(names: [])\n"
        "    val s: text = d.names[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".as_str");
}

TEST(field_access_self_in_method) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    name: text\n"
        "impl Obj:\n"
        "    fn get_name() -> text:\n"
        "        return self.name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->name");
}

TEST(field_access_self_array_index) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    data: [i64]\n"
        "impl Obj:\n"
        "    fn first() -> i64:\n"
        "        return self.data[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->data");
}

/* ================================================================
 * 20. Option Type Method/Field Access Edge Cases
 * ================================================================ */

TEST(option_unwrap_method) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    val opt: i64? = 5\n"
        "    return opt.unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt.value");
}

TEST(option_is_some_method) {
    auto out = compile_spl(
        "fn test() -> bool:\n"
        "    val opt: i64? = 5\n"
        "    return opt.is_some()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt.has_value");
}

TEST(option_is_none_method) {
    auto out = compile_spl(
        "fn test() -> bool:\n"
        "    val opt: i64? = nil\n"
        "    return opt.is_none()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "(!opt.has_value)");
}

TEST(option_struct_field_unwrap) {
    auto out = compile_spl(
        "struct Box:\n"
        "    value: i64?\n"
        "fn test(b: Box) -> i64:\n"
        "    return b.value.unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "b.value.value");
}

TEST(option_struct_field_is_some) {
    auto out = compile_spl(
        "struct Box:\n"
        "    value: i64?\n"
        "fn test(b: Box) -> bool:\n"
        "    return b.value.is_some()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "b.value.has_value");
}

/* ================================================================
 * 21. Single-Line If Edge Cases
 * ================================================================ */

TEST(single_line_if_return_nil_option) {
    auto out = compile_spl(
        "fn find() -> i64?:\n"
        "    if true: return nil\n"
        "    return 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {};");
}

TEST(single_line_if_break) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if i == 5: break\n"
    );
    ASSERT_CONTAINS(out.c_str(), "break;");
}

TEST(single_line_if_continue) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if i == 3: continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "continue;");
}

TEST(single_line_if_bare_return) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: return\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return;");
}

TEST(single_line_if_expression_stmt) {
    auto out = compile_spl(
        "fn setup():\n"
        "    pass\n"
        "fn test():\n"
        "    if true: setup()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "setup()");
}

/* ================================================================
 * 22. int() Built-In
 * ================================================================ */

TEST(int_builtin_call) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    val s: text = \"42\"\n"
        "    return int(s)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "atoll(s)");
}

/* ================================================================
 * 23. Parenthesized Expression Branches
 * ================================================================ */

TEST(paren_expr_grouping) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    return (1 + 2) * 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "(((1 + 2)) * 3)");
}

TEST(paren_empty_unit) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    return ()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "0 /* unit */");
}

/* ================================================================
 * 24. Type Inference Through Function/Method Calls
 * ================================================================ */

TEST(infer_fn_returning_text) {
    auto out = compile_spl(
        "fn get() -> text:\n"
        "    return \"x\"\n"
        "fn test():\n"
        "    val s = get()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

TEST(infer_fn_returning_bool) {
    auto out = compile_spl(
        "fn check() -> bool:\n"
        "    return true\n"
        "fn test():\n"
        "    val b = check()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

TEST(infer_fn_returning_array) {
    auto out = compile_spl(
        "fn items() -> [i64]:\n"
        "    var arr: [i64] = []\n"
        "    return arr\n"
        "fn test():\n"
        "    val a = items()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "SplArray* a");
}

TEST(infer_fn_returning_struct) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn origin() -> Pt:\n"
        "    return Pt(x: 0)\n"
        "fn test():\n"
        "    val p = origin()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

TEST(infer_option_coalescing_unwrap) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = 5\n"
        "    val v = opt ?? 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const int64_t v");
}

TEST(infer_text_method_trim) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val t = s.trim()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* t");
}

TEST(infer_text_method_contains) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val b = s.contains(\"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

TEST(infer_struct_field) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "    name: text\n"
        "fn test():\n"
        "    val p = Pt(x: 1, name: \"a\")\n"
        "    val n = p.name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* n");
}

TEST(infer_instance_method_return) {
    auto out = compile_spl(
        "struct Box:\n"
        "    v: i64\n"
        "impl Box:\n"
        "    fn get_v() -> i64:\n"
        "        return self.v\n"
        "fn test():\n"
        "    val b = Box(v: 1)\n"
        "    val x = b.get_v()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const int64_t x");
}

TEST(infer_static_method_return) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "impl Pt:\n"
        "    static fn zero() -> Pt:\n"
        "        return Pt(x: 0)\n"
        "fn test():\n"
        "    val p = Pt.zero()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

/* ================================================================
 * 25. Float Array Type Inference and Indexing
 * ================================================================ */

TEST(float_array_indexing) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [f64] = []\n"
        "    val v: f64 = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".as_float");
}

TEST(float_array_type_infer_from_index) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [f64] = []\n"
        "    val v = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "double v");
}

/* ================================================================
 * 26. Struct Array Element Type Inference
 * ================================================================ */

TEST(struct_array_index_infer) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
        "    val p = pts[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

TEST(struct_array_index_field_access) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "    name: text\n"
        "fn test():\n"
        "    var pts: [Pt] = []\n"
        "    val n = pts[0].name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* n");
}

/* ================================================================
 * 27. Array Literal Push Generation for Different Types
 * ================================================================ */

TEST(array_literal_text_pushes) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = [\"x\", \"y\"]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str(\"x\")");
    ASSERT_CONTAINS(out.c_str(), "spl_str(\"y\")");
}

TEST(array_literal_struct_pushes) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    var pts: [Pt] = [Pt(x: 1), Pt(x: 2)]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".push_back(");
}

/* ================================================================
 * 28. Module-Level Control Flow in __module_init
 * ================================================================ */

TEST(module_level_if_block) {
    auto out = compile_spl(
        "if true:\n"
        "    print \"init\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (true)");
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

TEST(module_level_while_block) {
    auto out = compile_spl(
        "var i: i64 = 0\n"
        "while i < 3:\n"
        "    i = i + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while (");
}

TEST(module_level_for_block) {
    auto out = compile_spl(
        "for i in 0..3:\n"
        "    print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (");
}

TEST(module_level_match_block) {
    auto out = compile_spl(
        "val x: i64 = 1\n"
        "match x:\n"
        "    case 1:\n"
        "        print \"one\"\n"
        "    case _:\n"
        "        print \"other\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
}

/* ================================================================
 * 29. Option Type Struct Generation Phases
 * ================================================================ */

TEST(option_primitive_struct_gen) {
    auto out = compile_spl(
        "fn test() -> i64?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "struct Option_i64");
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

TEST(option_struct_based_gen) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test() -> Pt?:\n"
        "    return nil\n"
    );
    /* Struct-based option is emitted after struct def */
    ASSERT_CONTAINS(out.c_str(), "struct Option_Pt");
    ASSERT_CONTAINS(out.c_str(), "struct Pt {");
}

/* ================================================================
 * 30. Comparison Operators Not Treated as Assignment
 * ================================================================ */

TEST(ne_not_treated_as_assign) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a != b\n"
    );
    /* != should not be treated as assignment */
    ASSERT_CONTAINS(out.c_str(), "!=");
    /* Ensure it's not translated to assignment "a = b;" */
    ASSERT_NOT_CONTAINS(out.c_str(), "a = b;");
}

TEST(le_not_treated_as_assign) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a <= b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "<=");
}

TEST(ge_not_treated_as_assign) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a >= b\n"
    );
    ASSERT_CONTAINS(out.c_str(), ">=");
}

TEST(eq_not_treated_as_assign) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a == b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "==");
}

/* ================================================================
 * Main: Run All Tests
 * ================================================================ */

int main(int argc, char** argv) {
    const char* env_seed = getenv("SEED_CPP");
    if (env_seed && env_seed[0]) {
        seed_binary = env_seed;
    } else {
        static char path[1024];
#ifdef _WIN32
        /* Try build-win directory */
        snprintf(path, sizeof(path), "seed_cpp.exe");
        FILE* f = fopen(path, "r");
        if (f) { fclose(f); seed_binary = path; }
        else {
            snprintf(path, sizeof(path), "seed\\build-win\\seed_cpp.exe");
            f = fopen(path, "r");
            if (f) { fclose(f); seed_binary = path; }
            else {
                snprintf(path, sizeof(path), "build-win\\seed_cpp.exe");
                f = fopen(path, "r");
                if (f) { fclose(f); seed_binary = path; }
                else {
                    fprintf(stderr, "Cannot find seed_cpp binary. Set SEED_CPP env var.\n");
                    return 1;
                }
            }
        }
#else
        snprintf(path, sizeof(path), "./seed_cpp");
        FILE* f = fopen(path, "r");
        if (f) { fclose(f); seed_binary = path; }
        else {
            snprintf(path, sizeof(path), "/tmp/seed_cpp");
            f = fopen(path, "r");
            if (f) { fclose(f); seed_binary = path; }
            else {
                fprintf(stderr, "Cannot find seed_cpp binary. Set SEED_CPP env var.\n");
                return 1;
            }
        }
#endif
    }

    printf("=== seed.cpp Branch Coverage Test Suite ===\n");
    printf("  seed binary: %s\n\n", seed_binary);

    printf("--- 1. String Interpolation Edge Cases ---\n");
    RUN(interp_multiple_adjacent);
    RUN(interp_with_expression);
    RUN(interp_trailing_text);
    RUN(interp_text_var_no_conversion);
    RUN(interp_mixed_types);
    RUN(interp_string_literal_expr);
    RUN(interp_three_segments);

    printf("\n--- 2. Operator Translation ---\n");
    RUN(op_and_translation);
    RUN(op_or_translation);
    RUN(op_not_translation);
    RUN(op_nil_coalescing_option);
    RUN(op_nil_coalescing_plain);
    RUN(op_string_plus_concatenation);
    RUN(op_nil_eq_text);
    RUN(op_nil_ne_text);
    RUN(op_nil_eq_int);
    RUN(op_nil_ne_int);
    RUN(op_nil_left_side_eq_option);
    RUN(op_nil_left_side_ne_option);

    printf("\n--- 3. Method Calls ---\n");
    RUN(method_len_on_text);
    RUN(method_len_on_array);
    RUN(method_len_on_struct_array);
    RUN(method_push_on_struct_array);
    RUN(method_push_on_nested_array);
    RUN(method_push_on_text_array);
    RUN(method_push_on_float_array);
    RUN(method_push_on_int_array);
    RUN(method_pop_on_struct_array);
    RUN(method_pop_on_int_array);
    RUN(method_contains_on_text);
    RUN(method_starts_with);
    RUN(method_ends_with);
    RUN(method_index_of);
    RUN(method_trim);
    RUN(method_replace);
    RUN(method_slice_on_text);

    printf("\n--- 4. Array Operations ---\n");
    RUN(array_literal_empty);
    RUN(array_literal_with_ints);
    RUN(array_literal_with_text);
    RUN(array_indexing_int);
    RUN(array_indexing_text);
    RUN(array_indexing_float);
    RUN(array_indexing_nested);
    RUN(array_indexing_struct);
    RUN(array_set_int);
    RUN(array_set_text);
    RUN(array_set_nested);
    RUN(array_set_struct);

    printf("\n--- 5. For Loop Variants ---\n");
    RUN(for_dotdot_range);
    RUN(for_range_one_arg);
    RUN(for_range_two_args);
    RUN(for_in_int_array);
    RUN(for_in_text_array);
    RUN(for_in_float_array);
    RUN(for_in_nested_array);
    RUN(for_in_struct_array);
    RUN(for_in_numeric_expr);

    printf("\n--- 6. Match/Case ---\n");
    RUN(match_simple_int);
    RUN(match_pipe_separated);
    RUN(match_enum_variant);
    RUN(match_pipe_with_enum_and_default);

    printf("\n--- 7. Variable Declarations ---\n");
    RUN(val_i64_explicit);
    RUN(var_i64_explicit);
    RUN(val_text_inferred);
    RUN(val_bool_inferred);
    RUN(val_array_inferred);
    RUN(val_struct_inferred);
    RUN(var_option_nil_init);
    RUN(var_option_value_init);
    RUN(val_struct_array);
    RUN(var_struct_array_init);

    printf("\n--- 8. Function Signatures ---\n");
    RUN(fn_multi_params);
    RUN(fn_typed_return);
    RUN(fn_void_implicit);
    RUN(fn_param_no_type_default_i64);
    RUN(extern_fn_declaration);
    RUN(extern_fn_multiple_params);

    printf("\n--- 9. Implicit Returns ---\n");
    RUN(implicit_return_expr);
    RUN(implicit_return_func_call);
    RUN(implicit_return_not_for_void);
    RUN(implicit_return_not_for_assignment);
    RUN(implicit_return_not_for_if);

    printf("\n--- 10. Assignment Operators ---\n");
    RUN(assign_plus_equals);
    RUN(assign_minus_equals);
    RUN(assign_array_element);
    RUN(assign_option_nil);
    RUN(assign_struct_array_clear);

    printf("\n--- 11. Control Flow ---\n");
    RUN(ctrl_break_in_for);
    RUN(ctrl_continue_in_for);
    RUN(ctrl_return_mid_function);
    RUN(ctrl_bare_return);
    RUN(ctrl_return_nil_from_option);

    printf("\n--- 12. Struct Methods ---\n");
    RUN(struct_method_self_field);
    RUN(struct_method_me_mutable);
    RUN(struct_method_static_no_self);
    RUN(struct_method_call_from_self);

    printf("\n--- 13. Print Statements ---\n");
    RUN(print_text_literal);
    RUN(print_int_var);
    RUN(print_text_var);
    RUN(print_interpolated_string);

    printf("\n--- 14. Module-Level Code ---\n");
    RUN(module_val_const_text);
    RUN(module_var_int_const);
    RUN(module_var_array);
    RUN(module_var_option);
    RUN(module_var_struct);
    RUN(module_var_dynamic_text);
    RUN(module_var_dynamic_bool);
    RUN(module_var_dynamic_int);
    RUN(module_level_fn_call);

    printf("\n--- 15. Type Conversions ---\n");
    RUN(type_i32);
    RUN(type_u8);
    RUN(type_u32);
    RUN(type_u64);
    RUN(type_f64);
    RUN(type_f32);
    RUN(type_bool);
    RUN(type_text);
    RUN(type_option_text);
    RUN(type_option_bool);
    RUN(type_option_array);
    RUN(type_enum_is_i64);
    RUN(type_struct_value);
    RUN(type_struct_array_vector);

    printf("\n--- 16. Empty/Edge Cases ---\n");
    RUN(empty_file);
    RUN(comment_only_file);
    RUN(empty_fn_body_with_pass);
    RUN(unit_expr_statement);

    printf("\n--- 17. Constructor Calls ---\n");
    RUN(constructor_named_fields);
    RUN(constructor_with_expr);
    RUN(constructor_with_string_field);

    printf("\n--- 18. Use/Export Directives ---\n");
    RUN(use_directive_skipped);
    RUN(export_directive_skipped);
    RUN(import_directive_skipped);
    RUN(use_inside_function_skipped);

    printf("\n--- 19. Struct Field Access ---\n");
    RUN(field_access_struct_array_index);
    RUN(field_access_struct_text_index);
    RUN(field_access_struct_text_slice);
    RUN(field_access_struct_text_array_element);
    RUN(field_access_self_in_method);
    RUN(field_access_self_array_index);

    printf("\n--- 20. Option Type Methods ---\n");
    RUN(option_unwrap_method);
    RUN(option_is_some_method);
    RUN(option_is_none_method);
    RUN(option_struct_field_unwrap);
    RUN(option_struct_field_is_some);

    printf("\n--- 21. Single-Line If ---\n");
    RUN(single_line_if_return_nil_option);
    RUN(single_line_if_break);
    RUN(single_line_if_continue);
    RUN(single_line_if_bare_return);
    RUN(single_line_if_expression_stmt);

    printf("\n--- 22. Built-in Functions ---\n");
    RUN(int_builtin_call);

    printf("\n--- 23. Parenthesized Expressions ---\n");
    RUN(paren_expr_grouping);
    RUN(paren_empty_unit);

    printf("\n--- 24. Type Inference ---\n");
    RUN(infer_fn_returning_text);
    RUN(infer_fn_returning_bool);
    RUN(infer_fn_returning_array);
    RUN(infer_fn_returning_struct);
    RUN(infer_option_coalescing_unwrap);
    RUN(infer_text_method_trim);
    RUN(infer_text_method_contains);
    RUN(infer_struct_field);
    RUN(infer_instance_method_return);
    RUN(infer_static_method_return);

    printf("\n--- 25. Float Arrays ---\n");
    RUN(float_array_indexing);
    RUN(float_array_type_infer_from_index);

    printf("\n--- 26. Struct Array Inference ---\n");
    RUN(struct_array_index_infer);
    RUN(struct_array_index_field_access);

    printf("\n--- 27. Array Literal Pushes ---\n");
    RUN(array_literal_text_pushes);
    RUN(array_literal_struct_pushes);

    printf("\n--- 28. Module-Level Control Flow ---\n");
    RUN(module_level_if_block);
    RUN(module_level_while_block);
    RUN(module_level_for_block);
    RUN(module_level_match_block);

    printf("\n--- 29. Option Struct Generation ---\n");
    RUN(option_primitive_struct_gen);
    RUN(option_struct_based_gen);

    printf("\n--- 30. Comparison Not Assignment ---\n");
    RUN(ne_not_treated_as_assign);
    RUN(le_not_treated_as_assign);
    RUN(ge_not_treated_as_assign);
    RUN(eq_not_treated_as_assign);

    printf("\n=== %d/%d tests passed ===\n", tests_passed, tests_run);
    return 0;
}
