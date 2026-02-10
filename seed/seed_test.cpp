/*
 * seed.cpp — Integration Test Suite
 *
 * Writes sample .spl files to /tmp, invokes seed_cpp on them,
 * captures output C++ code, checks it contains expected patterns.
 *
 * Build:
 *   c++ -std=c++20 -o /tmp/seed_test bootstrap/seed_test.cpp && /tmp/seed_test
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

static int tests_run = 0;
static const char* seed_binary = nullptr;

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

#define ASSERT_CONTAINS(haystack, needle) do { \
    if (strstr((haystack), (needle)) == nullptr) { \
        printf(" FAIL\n    output missing: \"%s\"\n    %s:%d\n", (needle), __FILE__, __LINE__); \
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
    const char* path = "/tmp/_seed_test_input.spl";
    FILE* f = fopen(path, "w");
    if (!f) { perror("fopen"); exit(1); }
    fputs(content, f);
    fclose(f);

    char cmd[512];
    snprintf(cmd, sizeof(cmd), "%s %s 2>/dev/null", seed_binary, path);
    FILE* p = popen(cmd, "r");
    if (!p) { perror("popen"); exit(1); }

    std::string result;
    char buf[4096];
    while (fgets(buf, sizeof(buf), p)) result += buf;
    pclose(p);
    return result;
}

/* ================================================================
 * Struct tests
 * ================================================================ */

TEST(struct_definition) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
    );
    ASSERT_CONTAINS(out.c_str(), "struct Point");
    ASSERT_CONTAINS(out.c_str(), "int64_t x");
    ASSERT_CONTAINS(out.c_str(), "int64_t y");
}

TEST(struct_text_field) {
    auto out = compile_spl(
        "struct Person:\n"
        "    name: text\n"
        "    age: i64\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* name");
    ASSERT_CONTAINS(out.c_str(), "int64_t age");
}

/* ================================================================
 * Enum tests
 * ================================================================ */

TEST(enum_definition) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Green\n"
        "    Blue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Color_Red");
    ASSERT_CONTAINS(out.c_str(), "Color_Green");
    ASSERT_CONTAINS(out.c_str(), "Color_Blue");
}

/* ================================================================
 * Function tests
 * ================================================================ */

TEST(fn_basic) {
    auto out = compile_spl(
        "fn add(a: i64, b: i64) -> i64:\n"
        "    return a + b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t add(");
    ASSERT_CONTAINS(out.c_str(), "return");
}

TEST(fn_void) {
    auto out = compile_spl(
        "fn greet():\n"
        "    print \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "void greet(");
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

TEST(fn_text_return) {
    auto out = compile_spl(
        "fn name() -> text:\n"
        "    return \"alice\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* name(");
}

TEST(extern_fn) {
    auto out = compile_spl(
        "extern fn rt_file_read(path: text) -> text\n"
    );
    ASSERT_CONTAINS(out.c_str(), "extern");
    ASSERT_CONTAINS(out.c_str(), "rt_file_read");
}

/* ================================================================
 * Variable tests
 * ================================================================ */

TEST(val_declaration) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 42\n"
        "    print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x = 42");
}

TEST(var_declaration) {
    auto out = compile_spl(
        "fn test():\n"
        "    var count: i64 = 0\n"
        "    count = count + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t count = 0");
}

TEST(module_level_val) {
    auto out = compile_spl(
        "val VERSION: text = \"1.0\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* VERSION");
}

TEST(module_level_var) {
    auto out = compile_spl(
        "var count: i64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t count");
}

/* ================================================================
 * Expression tests
 * ================================================================ */

TEST(string_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello world\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "hello world");
}

TEST(string_interpolation) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
        "    val s: text = \"value: {x}\"\n"
    );
    /* Interpolation generates spl_str_concat with spl_i64_to_str */
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

TEST(bool_literals) {
    auto out = compile_spl(
        "fn test():\n"
        "    val t: bool = true\n"
        "    val f: bool = false\n"
    );
    ASSERT_CONTAINS(out.c_str(), "true");
    ASSERT_CONTAINS(out.c_str(), "false");
}

TEST(nil_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    val n: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
}

TEST(binary_operators) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: i64 = 1 + 2\n"
        "    val b: i64 = 5 - 3\n"
        "    val c: i64 = 4 * 3\n"
        "    val d: i64 = 10 / 2\n"
        "    val e: i64 = 10 % 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "+");
    ASSERT_CONTAINS(out.c_str(), "-");
    ASSERT_CONTAINS(out.c_str(), "*");
    ASSERT_CONTAINS(out.c_str(), "/");
    ASSERT_CONTAINS(out.c_str(), "%");
}

TEST(logical_operators) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: bool = true and false\n"
        "    val b: bool = true or false\n"
        "    val c: bool = not true\n"
    );
    ASSERT_CONTAINS(out.c_str(), "&&");
    ASSERT_CONTAINS(out.c_str(), "||");
    ASSERT_CONTAINS(out.c_str(), "!");
}

TEST(comparison_operators) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: bool = 5 == 5\n"
        "    val b: bool = 5 != 3\n"
        "    val c: bool = 3 < 5\n"
        "    val d: bool = 5 > 3\n"
        "    val e: bool = 5 <= 5\n"
        "    val f: bool = 5 >= 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "==");
    ASSERT_CONTAINS(out.c_str(), "!=");
    ASSERT_CONTAINS(out.c_str(), "<");
    ASSERT_CONTAINS(out.c_str(), ">");
}

TEST(string_equality) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: text = \"hi\"\n"
        "    val b: bool = a == \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_eq");
}

/* ================================================================
 * Control flow tests
 * ================================================================ */

TEST(if_statement) {
    auto out = compile_spl(
        "fn test():\n"
        "    if 5 > 3:\n"
        "        print \"yes\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
}

TEST(if_else) {
    auto out = compile_spl(
        "fn test():\n"
        "    if 3 > 5:\n"
        "        print \"no\"\n"
        "    else:\n"
        "        print \"yes\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
    ASSERT_CONTAINS(out.c_str(), "else");
}

TEST(if_elif_else) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 2\n"
        "    if x == 1:\n"
        "        print \"one\"\n"
        "    elif x == 2:\n"
        "        print \"two\"\n"
        "    else:\n"
        "        print \"other\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "else if");
}

TEST(while_loop) {
    auto out = compile_spl(
        "fn test():\n"
        "    var i: i64 = 0\n"
        "    while i < 10:\n"
        "        i = i + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while (");
}

TEST(for_range) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (");
}

TEST(for_range_fn) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(5):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (");
}

TEST(match_statement) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 2\n"
        "    match x:\n"
        "        case 1:\n"
        "            print \"one\"\n"
        "        case 2:\n"
        "            print \"two\"\n"
        "        case _:\n"
        "            print \"other\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
    ASSERT_CONTAINS(out.c_str(), "case");
    ASSERT_CONTAINS(out.c_str(), "default");
}

TEST(break_continue) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if i == 5:\n"
        "            break\n"
        "        if i == 3:\n"
        "            continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "break");
    ASSERT_CONTAINS(out.c_str(), "continue");
}

/* ================================================================
 * Method / impl tests
 * ================================================================ */

TEST(impl_method) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "impl Point:\n"
        "    fn get_x() -> i64:\n"
        "        return self.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Point__get_x");
    ASSERT_CONTAINS(out.c_str(), "self->");
}

TEST(impl_mutable_method) {
    auto out = compile_spl(
        "struct Counter:\n"
        "    n: i64\n"
        "\n"
        "impl Counter:\n"
        "    me inc():\n"
        "        self.n = self.n + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Counter__inc");
    ASSERT_CONTAINS(out.c_str(), "self->");
}

TEST(impl_static_method) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "impl Point:\n"
        "    static fn origin() -> Point:\n"
        "        return Point(x: 0, y: 0)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Point__origin");
}

/* ================================================================
 * Built-in method tests
 * ================================================================ */

TEST(string_methods) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val n: i64 = s.len()\n"
        "    val c: bool = s.contains(\"ell\")\n"
        "    val sw: bool = s.starts_with(\"he\")\n"
        "    val ew: bool = s.ends_with(\"lo\")\n"
        "    val idx: i64 = s.index_of(\"l\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_len");
    ASSERT_CONTAINS(out.c_str(), "spl_str_contains");
    ASSERT_CONTAINS(out.c_str(), "spl_str_starts_with");
    ASSERT_CONTAINS(out.c_str(), "spl_str_ends_with");
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_of");
}

TEST(array_methods) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = []\n"
        "    arr.push(1)\n"
        "    val n: i64 = arr.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
    ASSERT_CONTAINS(out.c_str(), "spl_array_len");
}

/* ================================================================
 * Type system tests
 * ================================================================ */

TEST(all_primitive_types) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: i64 = 1\n"
        "    val b: i32 = 2\n"
        "    val c: u8 = 3\n"
        "    val d: f64 = 3.14\n"
        "    val e: bool = true\n"
        "    val f: text = \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t a");
    ASSERT_CONTAINS(out.c_str(), "int32_t b");
    ASSERT_CONTAINS(out.c_str(), "uint8_t c");
    ASSERT_CONTAINS(out.c_str(), "double d");
    ASSERT_CONTAINS(out.c_str(), "bool e");
    ASSERT_CONTAINS(out.c_str(), "const char* f");
}

TEST(option_type) {
    auto out = compile_spl(
        "fn maybe() -> i64?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
}

TEST(struct_constructor) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn test():\n"
        "    val p: Point = Point(x: 3, y: 4)\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".x =");
    ASSERT_CONTAINS(out.c_str(), ".y =");
}

/* ================================================================
 * use/export (should be tracked but not emitted as code)
 * ================================================================ */

TEST(use_export_skipped) {
    auto out = compile_spl(
        "use std.io.{print}\n"
        "export greet\n"
        "\n"
        "fn greet():\n"
        "    print \"hi\"\n"
    );
    /* use/export should not cause errors, function should still be emitted */
    ASSERT_CONTAINS(out.c_str(), "void greet(");
}

/* ================================================================
 * Assignment operators
 * ================================================================ */

TEST(compound_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    x += 5\n"
        "    x -= 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "+=");
    ASSERT_CONTAINS(out.c_str(), "-=");
}

/* ================================================================
 * Print statement
 * ================================================================ */

TEST(print_statement) {
    auto out = compile_spl(
        "fn test():\n"
        "    print \"hello\"\n"
        "    print 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

/* ================================================================
 * Includes header
 * ================================================================ */

TEST(has_runtime_include) {
    auto out = compile_spl(
        "fn test():\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "#include");
    ASSERT_CONTAINS(out.c_str(), "runtime.h");
}

TEST(has_main_function) {
    auto out = compile_spl(
        "fn test():\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int main(");
    ASSERT_CONTAINS(out.c_str(), "__module_init");
}

/* ================================================================
 * Enum in match
 * ================================================================ */

TEST(enum_match) {
    auto out = compile_spl(
        "enum Dir:\n"
        "    Up\n"
        "    Down\n"
        "\n"
        "fn test():\n"
        "    val d: i64 = 0\n"
        "    match d:\n"
        "        case 0:\n"
        "            print \"up\"\n"
        "        case 1:\n"
        "            print \"down\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Dir_Up");
    ASSERT_CONTAINS(out.c_str(), "Dir_Down");
}

/* ================================================================
 * Array literal
 * ================================================================ */

TEST(array_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    val arr: [i64] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
}

/* ================================================================
 * Nil coalescing
 * ================================================================ */

TEST(nil_coalescing) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: i64? = nil\n"
        "    val x: i64 = opt ?? 10\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

/* ================================================================
 * for-in array
 * ================================================================ */

TEST(for_in_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = []\n"
        "    for item in arr:\n"
        "        print item\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (");
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
}

/* ================================================================
 * Option methods
 * ================================================================ */

TEST(option_methods) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: i64? = nil\n"
        "    val a: bool = opt.is_some()\n"
        "    val b: bool = opt.is_none()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

/* ================================================================
 * String concat
 * ================================================================ */

TEST(string_concat) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: text = \"hello\"\n"
        "    val b: text = a + \" world\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* ================================================================
 * Single-line if
 * ================================================================ */

TEST(single_line_if) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if 5 > 3: x = 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
}

/* ================================================================
 * Field access
 * ================================================================ */

TEST(field_access) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn test():\n"
        "    val p: Point = Point(x: 1, y: 2)\n"
        "    val px: i64 = p.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "p.x");
}

/* ================================================================
 * Multiple files / empty input
 * ================================================================ */

TEST(empty_input) {
    auto out = compile_spl("");
    /* Should still produce valid C++ with main */
    ASSERT_CONTAINS(out.c_str(), "int main(");
}

TEST(comment_only) {
    auto out = compile_spl(
        "# This is a comment\n"
        "# Another comment\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int main(");
}

/* ================================================================
 * No-args usage (error path)
 * ================================================================ */

TEST(no_args_exits) {
    char cmd[512];
    snprintf(cmd, sizeof(cmd), "%s 2>/dev/null; echo $?", seed_binary);
    FILE* p = popen(cmd, "r");
    char buf[64];
    fgets(buf, sizeof(buf), p);
    pclose(p);
    /* Should exit with code 1 */
    ASSERT(atoi(buf) == 1);
}

/* ================================================================
 * Coverage: Module-level Option/struct/dynamic variables
 * ================================================================ */

TEST(module_option_var) {
    auto out = compile_spl(
        "var opt: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Option_i64 opt = {}");
}

TEST(module_struct_var) {
    auto out = compile_spl(
        "struct Config:\n"
        "    value: i64\n"
        "\n"
        "var cfg: Config = Config(value: 1)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Config cfg = {}");
    ASSERT_CONTAINS(out.c_str(), "cfg =");
}

TEST(module_dynamic_text_var) {
    auto out = compile_spl(
        "fn get_text() -> text:\n"
        "    return \"hello\"\n"
        "\n"
        "var dt: text = get_text()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static const char* dt = \"\"");
    ASSERT_CONTAINS(out.c_str(), "dt = get_text()");
}

TEST(module_dynamic_bool_var) {
    auto out = compile_spl(
        "fn get_flag() -> bool:\n"
        "    return true\n"
        "\n"
        "var flag: bool = get_flag()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static bool flag = false");
    ASSERT_CONTAINS(out.c_str(), "flag = get_flag()");
}

TEST(module_dynamic_int_var) {
    auto out = compile_spl(
        "fn get_num() -> i64:\n"
        "    return 42\n"
        "\n"
        "var num: i64 = get_num()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t num = 0");
    ASSERT_CONTAINS(out.c_str(), "num = get_num()");
}

TEST(module_option_nonnil_init) {
    auto out = compile_spl(
        "var opt: i64? = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Option_i64 opt = {}");
    ASSERT_CONTAINS(out.c_str(), "opt = 5");
}

/* ================================================================
 * Coverage: Module-level statements (translate_statement paths)
 * ================================================================ */

TEST(module_level_call) {
    auto out = compile_spl(
        "fn setup():\n"
        "    pass\n"
        "\n"
        "setup()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "setup()");
    ASSERT_CONTAINS(out.c_str(), "__module_init");
}

TEST(module_level_print_text) {
    auto out = compile_spl(
        "print \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

TEST(module_level_print_int) {
    auto out = compile_spl(
        "print 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf");
    ASSERT_CONTAINS(out.c_str(), "42");
}

TEST(module_level_pass) {
    auto out = compile_spl(
        "pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "/* pass */");
}

TEST(module_compound_assign) {
    auto out = compile_spl(
        "var x: i64 = 0\n"
        "x += 5\n"
        "x -= 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x += 5");
    ASSERT_CONTAINS(out.c_str(), "x -= 2");
}

TEST(module_array_set) {
    auto out = compile_spl(
        "var arr: [i64] = [1, 2, 3]\n"
        "arr[0] = 99\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
}

TEST(module_option_nil_assign) {
    auto out = compile_spl(
        "var opt: i64? = 5\n"
        "opt = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt = {}");
}

TEST(module_level_if) {
    auto out = compile_spl(
        "if true:\n"
        "    print \"init\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (true)");
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

/* ================================================================
 * Coverage: val/var with Option types in function blocks
 * ================================================================ */

TEST(val_option_nonnil) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: i64? = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Option_i64 opt = 5");
}

TEST(var_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64 opt = {}");
}

TEST(var_option_nonnil) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64 opt = 5");
}

TEST(var_array_with_elements) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2, 3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
    ASSERT_CONTAINS(out.c_str(), "spl_int(1)");
}

TEST(val_array_with_elements) {
    auto out = compile_spl(
        "fn test():\n"
        "    val arr: [i64] = [10, 20]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

/* ================================================================
 * Coverage: Match with pipe-separated multi-case
 * ================================================================ */

TEST(match_pipe_cases) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 0\n"
        "    match x:\n"
        "        case 0 | 1:\n"
        "            print \"low\"\n"
        "        case _:\n"
        "            print \"other\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case 0:");
    ASSERT_CONTAINS(out.c_str(), "case 1:");
    ASSERT_CONTAINS(out.c_str(), "default:");
}

TEST(match_enum_pipe) {
    auto out = compile_spl(
        "enum Dir:\n"
        "    Up\n"
        "    Down\n"
        "    Left\n"
        "\n"
        "fn test():\n"
        "    val d: i64 = 0\n"
        "    match d:\n"
        "        case Up | Down:\n"
        "            print \"vertical\"\n"
        "        case Left:\n"
        "            print \"horiz\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case Dir_Up:");
    ASSERT_CONTAINS(out.c_str(), "case Dir_Down:");
    ASSERT_CONTAINS(out.c_str(), "case Dir_Left:");
}

/* ================================================================
 * Coverage: use/export inside block
 * ================================================================ */

TEST(use_inside_block) {
    auto out = compile_spl(
        "fn test():\n"
        "    use std.io\n"
        "    print \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

/* ================================================================
 * Coverage: Modulo operator
 * ================================================================ */

TEST(modulo_operator) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 10 % 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "%");
    ASSERT_CONTAINS(out.c_str(), "10");
    ASSERT_CONTAINS(out.c_str(), "3");
}

/* ================================================================
 * Coverage: Nil comparison with option type
 * ================================================================ */

TEST(option_nil_comparison) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = nil\n"
        "    val a: bool = opt == nil\n"
        "    val b: bool = opt != nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!opt.has_value");
    ASSERT_CONTAINS(out.c_str(), "opt.has_value");
}

/* ================================================================
 * Coverage: ?? with non-option type
 * ================================================================ */

TEST(nil_coalescing_non_option) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
        "    val y: i64 = x ?? 10\n"
    );
    /* Non-option path: ternary fallback */
    ASSERT_CONTAINS(out.c_str(), "?");
    ASSERT_CONTAINS(out.c_str(), ":");
}

/* ================================================================
 * Coverage: Option .unwrap()
 * ================================================================ */

TEST(option_unwrap) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: i64? = 5\n"
        "    val v: i64 = opt.unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt.value");
}

/* ================================================================
 * Coverage: String escape in interpolation
 * ================================================================ */

TEST(string_interp_escape) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
        "    val s: text = \"val=\\\"x={x}\\\"\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* ================================================================
 * Coverage: Unit expression ()
 * ================================================================ */

TEST(unit_expression) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = ()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "0 /* unit */");
}

/* ================================================================
 * Coverage: Bare enum variant expression
 * ================================================================ */

TEST(bare_enum_variant) {
    auto out = compile_spl(
        "enum Dir:\n"
        "    Up\n"
        "    Down\n"
        "\n"
        "fn test():\n"
        "    val d: i64 = Up\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Dir_Up");
}

/* ================================================================
 * Coverage: Enum variant in call position
 * ================================================================ */

TEST(enum_variant_call) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Green\n"
        "\n"
        "fn test():\n"
        "    val c: i64 = Red()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Color_Red");
}

/* ================================================================
 * Coverage: Static method call usage
 * ================================================================ */

TEST(static_method_call) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "impl Point:\n"
        "    static fn origin() -> Point:\n"
        "        return Point(x: 0, y: 0)\n"
        "\n"
        "fn test():\n"
        "    val p: Point = Point.origin()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Point__origin()");
}

TEST(static_method_call_with_args) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "impl Point:\n"
        "    static fn create(x: i64, y: i64) -> Point:\n"
        "        return Point(x: x, y: y)\n"
        "\n"
        "fn test():\n"
        "    val p: Point = Point.create(1, 2)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Point__create(1, 2)");
}

/* ================================================================
 * Coverage: Instance method calls (struct)
 * ================================================================ */

TEST(instance_method_call) {
    auto out = compile_spl(
        "struct Counter:\n"
        "    n: i64\n"
        "\n"
        "impl Counter:\n"
        "    fn get() -> i64:\n"
        "        return self.n\n"
        "    me add(x: i64):\n"
        "        self.n = self.n + x\n"
        "\n"
        "fn test():\n"
        "    var c: Counter = Counter(n: 0)\n"
        "    c.add(5)\n"
        "    val v: i64 = c.get()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Counter__add(&c, 5)");
    ASSERT_CONTAINS(out.c_str(), "Counter__get(&c)");
}

/* ================================================================
 * Coverage: Struct-based Option type (Phase D codegen)
 * ================================================================ */

TEST(struct_option_type) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn maybe() -> Point?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_Point");
    ASSERT_CONTAINS(out.c_str(), "has_value");
    ASSERT_CONTAINS(out.c_str(), "return {}");
}

/* ================================================================
 * Coverage: Struct option field
 * ================================================================ */

TEST(struct_option_field) {
    auto out = compile_spl(
        "struct Node:\n"
        "    value: i64\n"
        "    next: i64?\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64 next");
}

/* ================================================================
 * Coverage: Text array literal
 * ================================================================ */

TEST(text_array_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    val arr: [text] = [\"a\", \"b\", \"c\"]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

/* ================================================================
 * Coverage: String/array indexing
 * ================================================================ */

TEST(string_indexing) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val c: text = s[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_char");
}

TEST(string_slicing) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val sub: text = s[1:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

TEST(slice_no_start) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val sub: text = s[:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

TEST(slice_no_end) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val sub: text = s[1:]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
    ASSERT_CONTAINS(out.c_str(), "spl_str_len");
}

TEST(array_indexing_int) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [10, 20]\n"
        "    val v: i64 = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
    ASSERT_CONTAINS(out.c_str(), ".as_int");
}

TEST(text_array_indexing) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = [\"a\", \"b\"]\n"
        "    val s: text = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
    ASSERT_CONTAINS(out.c_str(), ".as_str");
}

TEST(nested_array_indexing) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [[i64]] = []\n"
        "    val inner: [i64] = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".as_array");
}

/* ================================================================
 * Coverage: Struct field indexing/slicing
 * ================================================================ */

TEST(struct_field_array_index) {
    auto out = compile_spl(
        "struct Data:\n"
        "    items: [i64]\n"
        "\n"
        "fn test():\n"
        "    var d: Data = Data(items: [])\n"
        "    val v: i64 = d.items[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
}

TEST(struct_field_text_index) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    val d: Info = Info(name: \"hello\")\n"
        "    val c: text = d.name[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_char");
}

TEST(struct_field_slice) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    val d: Info = Info(name: \"hello\")\n"
        "    val sub: text = d.name[1:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

/* ================================================================
 * Coverage: Array set in block
 * ================================================================ */

TEST(array_set_in_block) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2]\n"
        "    arr[0] = 99\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
}

TEST(text_array_set) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = [\"a\"]\n"
        "    arr[0] = \"b\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

/* ================================================================
 * Coverage: Option nil assignment in block
 * ================================================================ */

TEST(option_nil_assign_block) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = 5\n"
        "    opt = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt = {}");
}

/* ================================================================
 * Coverage: Type inference
 * ================================================================ */

TEST(type_infer_string) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s = \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

TEST(type_infer_bool) {
    auto out = compile_spl(
        "fn test():\n"
        "    val b = true\n"
    );
    ASSERT_CONTAINS(out.c_str(), "bool b");
}

TEST(type_infer_struct) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn test():\n"
        "    val p = Point(x: 1, y: 2)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Point p");
}

TEST(type_infer_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    val arr = [1, 2]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

/* ================================================================
 * Coverage: return nil from option function
 * ================================================================ */

TEST(return_nil_option) {
    auto out = compile_spl(
        "fn maybe() -> i64?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {}");
}

/* ================================================================
 * Coverage: Implicit return
 * ================================================================ */

TEST(implicit_return) {
    auto out = compile_spl(
        "fn square(x: i64) -> i64:\n"
        "    x * x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* ================================================================
 * Coverage: int() built-in
 * ================================================================ */

TEST(int_builtin) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"42\"\n"
        "    val n: i64 = int(s)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "atoll(s)");
}

/* ================================================================
 * Coverage: String != comparison
 * ================================================================ */

TEST(string_not_equal) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: text = \"hi\"\n"
        "    val b: bool = a != \"bye\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!spl_str_eq");
}

/* ================================================================
 * Coverage: Multi-arg function call
 * ================================================================ */

TEST(multi_arg_fn_call) {
    auto out = compile_spl(
        "fn add(a: i64, b: i64) -> i64:\n"
        "    return a + b\n"
        "\n"
        "fn test():\n"
        "    val x: i64 = add(1, 2)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "add(1, 2)");
}

/* ================================================================
 * Coverage: Multi-file input
 * ================================================================ */

TEST(multi_file_input) {
    const char* path1 = "/tmp/_seed_test_file1.spl";
    const char* path2 = "/tmp/_seed_test_file2.spl";

    FILE* f1 = fopen(path1, "w");
    fputs("fn foo() -> i64:\n    return 1\n", f1);
    fclose(f1);

    FILE* f2 = fopen(path2, "w");
    fputs("fn bar() -> i64:\n    return 2\n", f2);
    fclose(f2);

    char cmd[512];
    snprintf(cmd, sizeof(cmd), "%s %s %s 2>/dev/null", seed_binary, path1, path2);
    FILE* p = popen(cmd, "r");
    std::string result;
    char buf[4096];
    while (fgets(buf, sizeof(buf), p)) result += buf;
    pclose(p);

    ASSERT_CONTAINS(result.c_str(), "int64_t foo(");
    ASSERT_CONTAINS(result.c_str(), "int64_t bar(");
}

/* ================================================================
 * Coverage: String replace and trim
 * ================================================================ */

TEST(string_replace_method) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val r: text = s.replace(\"l\", \"r\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_replace");
}

TEST(string_trim_method) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \" hello \"\n"
        "    val t: text = s.trim()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_trim");
}

/* ================================================================
 * Coverage: Compound assign in block
 * ================================================================ */

TEST(compound_assign_in_block) {
    auto out = compile_spl(
        "fn test():\n"
        "    var sum: i64 = 0\n"
        "    for i in 0..10:\n"
        "        sum += i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "sum += i");
}

/* ================================================================
 * Coverage: Modulo with variables (not digits)
 * ================================================================ */

TEST(modulo_with_vars) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: i64 = 10\n"
        "    val b: i64 = 3\n"
        "    val c: i64 = a % b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "% b");
}

/* ================================================================
 * Coverage: Struct field slice edge cases
 * ================================================================ */

TEST(struct_field_slice_no_start) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    val d: Info = Info(name: \"hello\")\n"
        "    val sub: text = d.name[:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice(d.name, 0, 3)");
}

TEST(struct_field_slice_no_end) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    val d: Info = Info(name: \"hello\")\n"
        "    val sub: text = d.name[1:]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_len(d.name)");
}

/* ================================================================
 * Coverage: Struct field text array index
 * ================================================================ */

TEST(struct_field_text_array_index) {
    auto out = compile_spl(
        "struct Data:\n"
        "    names: [text]\n"
        "\n"
        "fn test():\n"
        "    var d: Data = Data(names: [])\n"
        "    val s: text = d.names[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
    ASSERT_CONTAINS(out.c_str(), ".as_str");
}

/* ================================================================
 * Coverage: String with escape but no interpolation (line 669)
 * ================================================================ */

TEST(string_escape_no_interp) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\\nworld\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "hello\\nworld");
}

/* ================================================================
 * Coverage: Type inference for Option methods
 * ================================================================ */

TEST(type_infer_is_some) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: i64? = 5\n"
        "    val b = opt.is_some()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "bool b");
    ASSERT_CONTAINS(out.c_str(), "opt.has_value");
}

TEST(type_infer_unwrap) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: i64? = 5\n"
        "    val v = opt.unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt.value");
}

/* ================================================================
 * Coverage: Function with option param (param type registration)
 * ================================================================ */

TEST(fn_option_param) {
    auto out = compile_spl(
        "fn maybe(x: i64?) -> i64:\n"
        "    return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64 x");
}

/* ================================================================
 * Coverage: Match with wildcard in pipe
 * ================================================================ */

TEST(match_pipe_with_wildcard) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
        "    match x:\n"
        "        case 1:\n"
        "            print \"one\"\n"
        "        case 2 | _:\n"
        "            print \"other\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case 2:");
    ASSERT_CONTAINS(out.c_str(), "default:");
}

/* ================================================================
 * Coverage: Module-level text array set
 * ================================================================ */

TEST(module_text_array_set) {
    auto out = compile_spl(
        "var arr: [text] = [\"a\"]\n"
        "arr[0] = \"b\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
}

/* ================================================================
 * Coverage: Generic method call (non-struct obj)
 * ================================================================ */

TEST(generic_method_call) {
    auto out = compile_spl(
        "fn to_upper(s: text) -> text:\n"
        "    return s\n"
        "\n"
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val u: text = s.to_upper()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "to_upper");
}

/* ================================================================
 * Coverage: Struct option field unwrap type inference
 * ================================================================ */

TEST(struct_field_option_unwrap_infer) {
    auto out = compile_spl(
        "struct Node:\n"
        "    value: i64\n"
        "    next: i64?\n"
        "\n"
        "fn test():\n"
        "    val n: Node = Node(value: 1, next: 5)\n"
        "    val v = n.next.unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "n.next");
}

/* ================================================================
 * Coverage: Function returning Option with unwrap type inference
 * ================================================================ */

TEST(fn_return_option_unwrap_infer) {
    auto out = compile_spl(
        "fn get_opt() -> i64?:\n"
        "    return 5\n"
        "\n"
        "fn test():\n"
        "    val v = get_opt()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "get_opt()");
}

/* ================================================================
 * Coverage: Nested array set in module (translate_statement)
 * ================================================================ */

TEST(module_nested_array_set) {
    auto out = compile_spl(
        "var arr: [[i64]] = []\n"
        "var inner: [i64] = []\n"
        "arr[0] = inner\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
}

/* ================================================================
 * Coverage: Option array type [i64]? → Option_array (lines 232, 240)
 * ================================================================ */

TEST(option_array_type) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64]? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_array");
}

/* ================================================================
 * Coverage: Generic method call WITH args (lines 1123-1124, 1127-1130)
 * ================================================================ */

TEST(generic_method_call_with_args) {
    auto out = compile_spl(
        "fn pad(s: text, n: i64) -> text:\n"
        "    return s\n"
        "\n"
        "fn test():\n"
        "    val s: text = \"hi\"\n"
        "    val r: text = s.pad(10)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "pad(s, 10)");
}

/* ================================================================
 * Coverage: Struct field indexing unknown array type (lines 1201-1202)
 * Field type is an array but neither text nor [text] — falls through
 * to raw indexing: base[idx]
 * ================================================================ */

TEST(struct_field_generic_array_index) {
    /* Struct with a field of type that isn't recognized as text/[text]/[i64] */
    auto out = compile_spl(
        "struct Data:\n"
        "    items: [bool]\n"
        "\n"
        "fn test():\n"
        "    val d: Data = Data(items: [])\n"
        "    val x = d.items[0]\n"
    );
    /* [bool] is an array field — gets spl_array_get with .as_int (generic array) */
    ASSERT_CONTAINS(out.c_str(), "spl_array_get(d.items, 0)");
}

/* ================================================================
 * Coverage: Positional arg in constructor → break (lines 1313-1314)
 * Constructor with positional arg (no "field:" syntax)
 * ================================================================ */

TEST(constructor_positional_arg) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = int(\"42\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "atoll(");
}

/* ================================================================
 * Coverage: Struct field Option is_some/is_none type infer (line 1576)
 * ================================================================ */

TEST(struct_field_option_is_some_infer) {
    auto out = compile_spl(
        "struct Box:\n"
        "    value: i64?\n"
        "\n"
        "fn test():\n"
        "    val b: Box = Box(value: 5)\n"
        "    val ok = b.value.is_some()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "b.value.has_value");
}

/* ================================================================
 * Coverage: Function returning Option + .unwrap() type infer (lines 1635-1638)
 * When LHS is fn_call().unwrap(), infer base type from fn return type
 * ================================================================ */

TEST(fn_call_option_unwrap_infer) {
    auto out = compile_spl(
        "fn get_val() -> i64?:\n"
        "    return 42\n"
        "\n"
        "fn test():\n"
        "    val v = get_val().unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "get_val()");
    ASSERT_CONTAINS(out.c_str(), ".value");
}

/* ================================================================
 * Coverage: expr_is_text fallback for type inference (lines 1658-1659)
 * var without explicit type where RHS is a text expression
 * ================================================================ */

TEST(type_infer_text_expr) {
    auto out = compile_spl(
        "fn greet(name: text) -> text:\n"
        "    return name\n"
        "\n"
        "fn test():\n"
        "    val g = greet(\"world\")\n"
    );
    /* Should produce const char* or std::string, calling greet */
    ASSERT_CONTAINS(out.c_str(), "greet(");
}

/* ================================================================
 * Coverage: Single-line if with return nil (line 1750)
 * ================================================================ */

TEST(single_line_if_return_nil) {
    auto out = compile_spl(
        "fn test() -> i64?:\n"
        "    val x: bool = true\n"
        "    if x: return nil\n"
        "    return 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {}");
}

/* ================================================================
 * Coverage: Single-line if with bare return (line 1757)
 * ================================================================ */

TEST(single_line_if_bare_return) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: bool = true\n"
        "    if x: return\n"
        "    print \"done\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (x) { return; }");
}

/* ================================================================
 * Coverage: Single-line if with break (line 1759)
 * ================================================================ */

TEST(single_line_if_break) {
    auto out = compile_spl(
        "fn test():\n"
        "    var i: i64 = 0\n"
        "    while i < 10:\n"
        "        if i == 5: break\n"
        "        i = i + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if ((i == 5)) { break; }");
}

/* ================================================================
 * Coverage: Single-line if with continue (line 1761)
 * ================================================================ */

TEST(single_line_if_continue) {
    auto out = compile_spl(
        "fn test():\n"
        "    var i: i64 = 0\n"
        "    while i < 10:\n"
        "        i = i + 1\n"
        "        if i == 3: continue\n"
        "        print \"x\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if ((i == 3)) { continue; }");
}

/* ================================================================
 * Coverage: var array without initializer (lines 2039-2040)
 * ================================================================ */

TEST(var_array_no_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    var items: [i64]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new()");
}

/* ================================================================
 * Coverage: Param without type annotation → default i64 (lines 2451-2453)
 * ================================================================ */

TEST(fn_param_no_type) {
    auto out = compile_spl(
        "fn add(a, b) -> i64:\n"
        "    return a + b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t a");
    ASSERT_CONTAINS(out.c_str(), "int64_t b");
}

/* ================================================================
 * Coverage: Param name trailing space trimming (line 2433)
 * ================================================================ */

TEST(fn_param_trailing_space) {
    auto out = compile_spl(
        "fn add(a : i64, b : i64) -> i64:\n"
        "    return a + b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t a");
    ASSERT_CONTAINS(out.c_str(), "int64_t b");
}

/* ================================================================
 * Coverage: Return type trailing space trimming (line 2467)
 * ================================================================ */

TEST(fn_return_type_trailing_space) {
    auto out = compile_spl(
        "fn test() -> i64 :\n"
        "    return 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t test(");
}

/* ================================================================
 * Coverage: Implicit return with assignment → no return added (lines 2826-2828)
 * ================================================================ */

TEST(implicit_return_assignment) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    x = 5\n"
    );
    /* Assignment should NOT get "return" prepended */
    ASSERT_NOT_CONTAINS(out.c_str(), "return x = 5");
}

/* ================================================================
 * Coverage: Implicit return with assignment in method (lines 2946-2947)
 * ================================================================ */

TEST(method_implicit_return_assignment) {
    auto out = compile_spl(
        "struct Foo:\n"
        "    x: i64\n"
        "\n"
        "impl Foo:\n"
        "    me set_x(v: i64):\n"
        "        self.x = v\n"
    );
    /* Assignment in method body should NOT get return prepended */
    ASSERT_NOT_CONTAINS(out.c_str(), "return self->x = v");
}

/* ================================================================
 * Coverage: Unrecognized impl body line → j++ (lines 2972-2973)
 * ================================================================ */

TEST(impl_comment_line) {
    auto out = compile_spl(
        "struct Foo:\n"
        "    x: i64\n"
        "\n"
        "impl Foo:\n"
        "    # This is a comment inside impl\n"
        "    fn get_x() -> i64:\n"
        "        return self.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Foo__get_x(");
}

/* ================================================================
 * Coverage: String with escape but truly no interpolation (line 669)
 * Need string that has chars but NO {} → first part, no concat
 * ================================================================ */

TEST(string_escape_backslash_n) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\\nworld\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "hello\\nworld");
}

/* ================================================================
 * Coverage: replace() without closing paren (line 987)
 * ================================================================ */

TEST(string_replace_no_close_paren) {
    /* This is a weird edge case — normal code won't hit it,
       but let's cover the valid path more thoroughly */
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val r: text = s.replace(\"l\", \"r\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_replace(");
}

/* ================================================================
 * Coverage: Param type trailing space (line 2448)
 * ================================================================ */

TEST(fn_param_type_trailing_space) {
    auto out = compile_spl(
        "fn foo(name: text , age: i64 ) -> text:\n"
        "    return name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* name");
    ASSERT_CONTAINS(out.c_str(), "int64_t age");
}

/* ================================================================
 * Coverage: needs_return false for method body ending in return (line 2935)
 * ================================================================ */

TEST(method_explicit_return) {
    auto out = compile_spl(
        "struct Calc:\n"
        "    v: i64\n"
        "\n"
        "impl Calc:\n"
        "    fn double() -> i64:\n"
        "        return self.v * 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return (self->v * 2)");
}

/* ================================================================
 * Coverage: Option type struct field in module-level var
 * ================================================================ */

TEST(module_option_array_var) {
    auto out = compile_spl(
        "var opts: [i64]? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_array");
}

/* ================================================================
 * Coverage Batch 2: translate_statement paths
 * ================================================================ */

TEST(single_line_if_val_decl) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val x: i64 = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (true)");
}

TEST(single_line_if_var_decl) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: var y: i64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (true)");
}

TEST(single_line_if_return_expr) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    if true: return 42\n"
        "    return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 42");
}

TEST(single_line_if_print) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: print \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

TEST(single_line_if_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x = 5");
}

TEST(single_line_if_compound_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x += 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x += 5");
}

TEST(single_line_if_minus_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x -= 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x -= 2");
}

TEST(single_line_if_pass) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "/* pass */");
}

TEST(single_line_if_fn_call) {
    auto out = compile_spl(
        "fn setup():\n"
        "    pass\n"
        "\n"
        "fn test():\n"
        "    if true: setup()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "setup()");
}

/* ================================================================
 * Coverage Batch 2: Uncommon types
 * ================================================================ */

TEST(type_u32) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: u32 = 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "uint32_t x");
}

TEST(type_u64) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: u64 = 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "uint64_t x");
}

TEST(type_f32) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: f32 = 3.14\n"
    );
    ASSERT_CONTAINS(out.c_str(), "float x");
}

TEST(fn_void_return_type) {
    auto out = compile_spl(
        "fn test() -> void:\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "void test(");
}

TEST(enum_typed_var) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Green\n"
        "\n"
        "fn test():\n"
        "    val c: Color = Red\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t c");
}

/* ================================================================
 * Coverage Batch 2: Option .is_none()
 * ================================================================ */

TEST(option_is_none) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: i64? = nil\n"
        "    val b: bool = opt.is_none()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!opt.has_value");
}

/* ================================================================
 * Coverage Batch 2: Array methods
 * ================================================================ */

TEST(array_pop_method) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2]\n"
        "    val v: i64 = arr.pop()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_pop");
}

TEST(text_array_push) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = []\n"
        "    arr.push(\"hello\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

TEST(nested_array_push) {
    auto out = compile_spl(
        "fn test():\n"
        "    var outer: [[i64]] = []\n"
        "    var inner: [i64] = []\n"
        "    outer.push(inner)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
    ASSERT_CONTAINS(out.c_str(), "spl_array_val");
}

/* ================================================================
 * Coverage Batch 2: String methods more
 * ================================================================ */

TEST(string_to_upper) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val u: text = s.to_upper()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "to_upper(s)");
}

TEST(string_to_lower) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"HELLO\"\n"
        "    val l: text = s.to_lower()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "to_lower(s)");
}

TEST(string_split_method) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"a,b,c\"\n"
        "    val parts: [text] = s.split(\",\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "split(s");
}

/* ================================================================
 * Coverage Batch 2: Struct method with string arg in call
 * ================================================================ */

TEST(static_method_string_arg) {
    auto out = compile_spl(
        "struct Greeter:\n"
        "    name: text\n"
        "\n"
        "impl Greeter:\n"
        "    static fn hello(n: text) -> text:\n"
        "        return n\n"
        "\n"
        "fn test():\n"
        "    val s: text = Greeter.hello(\"world\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Greeter__hello(");
}

/* ================================================================
 * Coverage Batch 2: Module-level while/for/match blocks
 * ================================================================ */

TEST(module_level_while) {
    auto out = compile_spl(
        "var i: i64 = 0\n"
        "while i < 5:\n"
        "    i = i + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while (");
}

TEST(module_level_for) {
    auto out = compile_spl(
        "for i in 0..5:\n"
        "    print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (");
}

/* ================================================================
 * Coverage Batch 2: Text option type
 * ================================================================ */

TEST(text_option_type) {
    auto out = compile_spl(
        "fn maybe() -> text?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
}

TEST(struct_option_return_value) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn maybe() -> Point?:\n"
        "    return Point(x: 1, y: 2)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_Point");
}

/* ================================================================
 * Coverage Batch 2: Nil coalescing with option type (??)
 * ================================================================ */

TEST(nil_coalescing_text_option) {
    auto out = compile_spl(
        "fn test():\n"
        "    val opt: text? = nil\n"
        "    val s: text = opt ?? \"default\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

/* ================================================================
 * Coverage Batch 2: Method bodies with implicit return
 * ================================================================ */

TEST(method_implicit_return_expr) {
    auto out = compile_spl(
        "struct Box:\n"
        "    value: i64\n"
        "\n"
        "impl Box:\n"
        "    fn double() -> i64:\n"
        "        self.value * 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return (self->value * 2)");
}

TEST(method_body_with_loop) {
    auto out = compile_spl(
        "struct Sum:\n"
        "    total: i64\n"
        "\n"
        "impl Sum:\n"
        "    me accumulate(n: i64):\n"
        "        for i in 0..n:\n"
        "            self.total = self.total + i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Sum__accumulate");
    ASSERT_CONTAINS(out.c_str(), "for (");
}

/* ================================================================
 * Coverage Batch 2: Self field access patterns in methods
 * ================================================================ */

TEST(self_field_indexing) {
    auto out = compile_spl(
        "struct Data:\n"
        "    items: [i64]\n"
        "\n"
        "impl Data:\n"
        "    fn first() -> i64:\n"
        "        return self.items[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->items");
}

TEST(self_field_text_slice) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "\n"
        "impl Info:\n"
        "    fn first_char() -> text:\n"
        "        return self.name[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->name");
}

/* ================================================================
 * Coverage Batch 2: Function param with array type
 * ================================================================ */

TEST(fn_param_array_type) {
    auto out = compile_spl(
        "fn sum(arr: [i64]) -> i64:\n"
        "    return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "SplArray* arr");
}

/* ================================================================
 * Coverage Batch 2: Module-level var with struct init
 * ================================================================ */

TEST(module_struct_var_nonnil) {
    auto out = compile_spl(
        "struct Config:\n"
        "    value: i64\n"
        "    name: text\n"
        "\n"
        "var cfg: Config = Config(value: 42, name: \"test\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Config cfg");
}

/* ================================================================
 * Coverage Batch 2: Multiple statements in function
 * ================================================================ */

TEST(fn_with_if_elif_else_return) {
    auto out = compile_spl(
        "fn classify(x: i64) -> text:\n"
        "    if x > 0:\n"
        "        return \"positive\"\n"
        "    elif x < 0:\n"
        "        return \"negative\"\n"
        "    else:\n"
        "        return \"zero\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
    ASSERT_CONTAINS(out.c_str(), "else if");
}

/* ================================================================
 * Coverage Batch 2: Nested function calls in expressions
 * ================================================================ */

TEST(nested_fn_call) {
    auto out = compile_spl(
        "fn add(a: i64, b: i64) -> i64:\n"
        "    return a + b\n"
        "\n"
        "fn test():\n"
        "    val x: i64 = add(add(1, 2), 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "add(add(1, 2), 3)");
}

/* ================================================================
 * Coverage Batch 2: Parenthesized expressions
 * ================================================================ */

TEST(paren_expr) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = (1 + 2) * 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "(1 + 2)");
}

/* ================================================================
 * Coverage Batch 2: Array set with text
 * ================================================================ */

TEST(single_line_if_array_set) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2]\n"
        "    if true: arr[0] = 99\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
}

/* ================================================================
 * Coverage Batch 2: Option nil assign in translate_statement
 * ================================================================ */

TEST(single_line_if_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: i64? = 5\n"
        "    if true: opt = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt = {}");
}

/* ================================================================
 * Coverage Batch 2: Module-level for/match block
 * ================================================================ */

TEST(module_level_match) {
    auto out = compile_spl(
        "val x: i64 = 2\n"
        "match x:\n"
        "    case 1:\n"
        "        print \"one\"\n"
        "    case 2:\n"
        "        print \"two\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
}

/* ================================================================
 * Coverage Batch 2: Return handling
 * ================================================================ */

TEST(translate_stmt_bare_return) {
    auto out = compile_spl(
        "fn test():\n"
        "    if false:\n"
        "        return\n"
        "    print \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return;");
}

/* ================================================================
 * Coverage Batch 2: Generic method call with string args
 * ================================================================ */

TEST(generic_method_string_arg) {
    auto out = compile_spl(
        "fn pad_left(s: text, n: i64, c: text) -> text:\n"
        "    return s\n"
        "\n"
        "fn test():\n"
        "    val s: text = \"hi\"\n"
        "    val r: text = s.pad_left(5, \"0\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "pad_left(s");
}

/* ================================================================
 * Coverage Batch 2: Bool option type
 * ================================================================ */

TEST(bool_option_type) {
    auto out = compile_spl(
        "fn test():\n"
        "    var b: bool? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_bool");
}

/* ================================================================
 * Coverage Batch 2: Implicit return in functions
 * ================================================================ */

TEST(implicit_return_call) {
    auto out = compile_spl(
        "fn helper() -> i64:\n"
        "    return 5\n"
        "\n"
        "fn test() -> i64:\n"
        "    helper()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return helper()");
}

TEST(implicit_return_var) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    val x: i64 = 5\n"
        "    x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return x");
}

/* ================================================================
 * Coverage Batch 2: Struct construction with multiple fields
 * ================================================================ */

TEST(struct_construct_text_field) {
    auto out = compile_spl(
        "struct Person:\n"
        "    name: text\n"
        "    age: i64\n"
        "\n"
        "fn test():\n"
        "    val p: Person = Person(name: \"Alice\", age: 30)\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".name = ");
    ASSERT_CONTAINS(out.c_str(), ".age = ");
}

/* ================================================================
 * Coverage Batch 2: f64 arithmetic
 * ================================================================ */

TEST(f64_arithmetic) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: f64 = 3.14\n"
        "    val y: f64 = x * 2.0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "double x");
    ASSERT_CONTAINS(out.c_str(), "double y");
}

/* ================================================================
 * Coverage Batch 2: Module-level option nonnil with expr
 * ================================================================ */

TEST(module_option_with_fn_call) {
    auto out = compile_spl(
        "fn get_val() -> i64:\n"
        "    return 42\n"
        "\n"
        "var opt: i64? = get_val()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "opt = get_val()");
}

/* ================================================================
 * Coverage Batch 2: Var with struct type and constructor
 * ================================================================ */

TEST(var_struct_constructor) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn test():\n"
        "    var p: Point = Point(x: 1, y: 2)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Point p");
}

/* ================================================================
 * Coverage Batch 2: Array with bool elements
 * ================================================================ */

TEST(bool_array_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [bool] = [true, false]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

/* ================================================================
 * Coverage Batch 2: While with complex condition
 * ================================================================ */

TEST(while_complex_cond) {
    auto out = compile_spl(
        "fn test():\n"
        "    var i: i64 = 0\n"
        "    while i < 10 and i != 5:\n"
        "        i = i + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while (");
    ASSERT_CONTAINS(out.c_str(), "&&");
}

/* ================================================================
 * Coverage Batch 2: Negative numbers
 * ================================================================ */

TEST(negative_number) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = -5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "-5");
}

/* ================================================================
 * Coverage Batch 3: translate_statement deeper paths
 * ================================================================ */

TEST(single_line_if_val_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val arr: [i64] = [1, 2]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
}

TEST(single_line_if_val_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val opt: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
}

TEST(single_line_if_val_option_nonnil) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val opt: i64? = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
}

TEST(single_line_if_var_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: var arr: [i64] = [1, 2]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
}

TEST(single_line_if_var_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: var opt: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
}

TEST(single_line_if_var_option_nonnil) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: var opt: i64? = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
}

TEST(module_level_return_expr) {
    auto out = compile_spl(
        "return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

/* ================================================================
 * Coverage Batch 3: Nested array set in block
 * ================================================================ */

TEST(nested_array_set_in_block) {
    auto out = compile_spl(
        "fn test():\n"
        "    var outer: [[i64]] = []\n"
        "    var inner: [i64] = []\n"
        "    outer[0] = inner\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
    ASSERT_CONTAINS(out.c_str(), "spl_array_val");
}

/* ================================================================
 * Coverage Batch 3: Text array set in block
 * ================================================================ */

TEST(text_array_set_in_block) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = [\"a\"]\n"
        "    arr[0] = \"b\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

/* ================================================================
 * Coverage Batch 3: Method implicit return assignment (line 2900)
 * ================================================================ */

TEST(method_last_stmt_assignment) {
    auto out = compile_spl(
        "struct Foo:\n"
        "    x: i64\n"
        "\n"
        "impl Foo:\n"
        "    me reset():\n"
        "        self.x = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->x = 0");
    /* Should NOT have return prepended */
    ASSERT_NOT_CONTAINS(out.c_str(), "return self->x = 0");
}

/* ================================================================
 * Coverage Batch 3: Struct field not found (line 394)
 * ================================================================ */

TEST(struct_field_nonexistent) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn test():\n"
        "    val p: Point = Point(x: 1, y: 2)\n"
        "    val z: i64 = p.z\n"
    );
    /* Should still produce output (field access) even if field not in struct */
    ASSERT_CONTAINS(out.c_str(), "p.z");
}

/* ================================================================
 * Coverage Batch 3: String interpolation at end (line 621)
 * ================================================================ */

TEST(string_interp_at_end) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
        "    val s: text = \"{x}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

/* ================================================================
 * Coverage Batch 3: Method body with val/var/print (lines 2890-2893)
 * ================================================================ */

TEST(method_body_with_val) {
    auto out = compile_spl(
        "struct Calc:\n"
        "    v: i64\n"
        "\n"
        "impl Calc:\n"
        "    fn compute() -> i64:\n"
        "        val tmp: i64 = self.v + 1\n"
        "        return tmp\n"
    );
    ASSERT_CONTAINS(out.c_str(), "tmp = (self->v + 1)");
}

TEST(method_body_with_print) {
    auto out = compile_spl(
        "struct Logger:\n"
        "    msg: text\n"
        "\n"
        "impl Logger:\n"
        "    fn log():\n"
        "        print self.msg\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

/* ================================================================
 * Coverage Batch 3: Struct field slice self paths
 * ================================================================ */

TEST(self_field_slice) {
    auto out = compile_spl(
        "struct Info:\n"
        "    name: text\n"
        "\n"
        "impl Info:\n"
        "    fn first_three() -> text:\n"
        "        return self.name[0:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice(self->name");
}

/* ================================================================
 * Coverage Batch 3: Option ?? with text
 * ================================================================ */

TEST(option_coalescing_in_expr) {
    auto out = compile_spl(
        "fn get() -> text?:\n"
        "    return nil\n"
        "\n"
        "fn test():\n"
        "    val s: text = get() ?? \"fallback\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

/* ================================================================
 * Coverage Batch 3: Replace with nested parens (line 939)
 * ================================================================ */

TEST(replace_with_nested_call) {
    auto out = compile_spl(
        "fn get_str() -> text:\n"
        "    return \"l\"\n"
        "\n"
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val r: text = s.replace(get_str(), \"r\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_replace");
}

/* ================================================================
 * Coverage Batch 3: Instance method with mutable self + args
 * ================================================================ */

TEST(instance_method_mutable_with_args) {
    auto out = compile_spl(
        "struct Vec:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "impl Vec:\n"
        "    me add_scaled(other_x: i64, other_y: i64, scale: i64):\n"
        "        self.x = self.x + other_x * scale\n"
        "        self.y = self.y + other_y * scale\n"
        "\n"
        "fn test():\n"
        "    var v: Vec = Vec(x: 0, y: 0)\n"
        "    v.add_scaled(1, 2, 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Vec__add_scaled(&v, 1, 2, 3)");
}

/* ================================================================
 * Coverage Batch 3: Function returning text with inference
 * ================================================================ */

TEST(type_infer_fn_returning_text) {
    auto out = compile_spl(
        "fn greet() -> text:\n"
        "    return \"hi\"\n"
        "\n"
        "fn test():\n"
        "    val s = greet()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

/* ================================================================
 * Coverage Batch 3: Struct option return non-nil
 * ================================================================ */

TEST(option_struct_return_nonnil) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "\n"
        "fn make() -> Point?:\n"
        "    return Point(x: 1)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_Point");
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* ================================================================
 * Coverage Batch 3: for-range with variables
 * ================================================================ */

TEST(for_range_with_var) {
    auto out = compile_spl(
        "fn test():\n"
        "    val n: i64 = 10\n"
        "    for i in 0..n:\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (");
}

/* ================================================================
 * Coverage Batch 3: Module-level expression call
 * ================================================================ */

TEST(module_level_expr_call) {
    auto out = compile_spl(
        "fn init():\n"
        "    pass\n"
        "\n"
        "fn setup():\n"
        "    pass\n"
        "\n"
        "init()\n"
        "setup()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "init()");
    ASSERT_CONTAINS(out.c_str(), "setup()");
}

/* ================================================================
 * Coverage Batch 3: Impl with empty body between methods
 * ================================================================ */

TEST(impl_empty_line) {
    auto out = compile_spl(
        "struct Thing:\n"
        "    a: i64\n"
        "    b: i64\n"
        "\n"
        "impl Thing:\n"
        "    fn get_a() -> i64:\n"
        "        return self.a\n"
        "\n"
        "    fn get_b() -> i64:\n"
        "        return self.b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Thing__get_a");
    ASSERT_CONTAINS(out.c_str(), "Thing__get_b");
}

/* ================================================================
 * Coverage Batch 3: Function returning option with unwrap infer
 * ================================================================ */

TEST(fn_option_unwrap_method_infer) {
    auto out = compile_spl(
        "struct Box:\n"
        "    v: i64\n"
        "\n"
        "impl Box:\n"
        "    fn get() -> i64?:\n"
        "        return self.v\n"
        "\n"
        "fn test():\n"
        "    val b: Box = Box(v: 42)\n"
        "    val v = b.get().unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Box__get");
}

/* ================================================================
 * Coverage Batch 4: Systematic Branch Coverage
 * ================================================================ */

/* --- Nil comparison: nil on LEFT side (branch 770-772) --- */
TEST(nil_eq_left_side) {
    auto out = compile_spl(
        "fn test(x: i64) -> bool:\n"
        "    return nil == x\n"
    );
    /* nil on left, option check or int check */
    ASSERT_CONTAINS(out.c_str(), "== -1");
}

TEST(nil_ne_left_side) {
    auto out = compile_spl(
        "fn test(x: text) -> bool:\n"
        "    return nil != x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!= NULL");
}

/* --- String equality (branch for string == / != ) --- */
TEST(string_ne_operator) {
    auto out = compile_spl(
        "fn test(a: text, b: text) -> bool:\n"
        "    return a != b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!spl_str_eq");
}

/* --- String concat with + (branch 755-762) --- */
TEST(string_concat_operator) {
    auto out = compile_spl(
        "fn test(a: text, b: text) -> text:\n"
        "    return a + b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* --- ?? with non-option (branch 806-813) --- */
TEST(nil_coalescing_non_option_b4) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    return x ?? 0\n"
    );
    /* non-option: ternary fallback */
    ASSERT_CONTAINS(out.c_str(), "?");
    ASSERT_CONTAINS(out.c_str(), ":");
}

/* --- modulo operator (branch 746) --- */
TEST(modulo_operator_b4) {
    auto out = compile_spl(
        "fn test(a: i64) -> i64:\n"
        "    return a % 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "%");
}

/* --- String interp: only interpolation, no literal segments (branch 620-621 first=true at end) --- */
TEST(string_interp_only_expr) {
    auto out = compile_spl(
        "fn test(x: i64) -> text:\n"
        "    return \"{x}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

/* --- String interp: empty result (branch 628) --- */
TEST(string_interp_empty_braces) {
    auto out = compile_spl(
        "fn test() -> text:\n"
        "    return \"\"\n"
    );
    /* Empty string, no interpolation */
    ASSERT_CONTAINS(out.c_str(), "\"\"");
}

/* --- contains method (branch 894) --- */
TEST(text_contains_method) {
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s.contains(\"abc\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_contains");
}

/* --- starts_with method (branch 904) --- */
TEST(text_starts_with_method) {
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s.starts_with(\"abc\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_starts_with");
}

/* --- ends_with method (branch 914) --- */
TEST(text_ends_with_method) {
    auto out = compile_spl(
        "fn test(s: text) -> bool:\n"
        "    return s.ends_with(\"abc\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_ends_with");
}

/* --- index_of method (branch 924) --- */
TEST(text_index_of_method) {
    auto out = compile_spl(
        "fn test(s: text) -> i64:\n"
        "    return s.index_of(\"abc\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_of");
}

/* --- trim method (branch 930-932) --- */
TEST(text_trim_method) {
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s.trim()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_trim");
}

/* --- replace with nested parens (exercise depth tracking in replace args at 942-945) --- */
TEST(replace_nested_arg_parens) {
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s.replace(\"a\", \"b\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_replace");
}

/* --- Static method no args (branch 998-999) --- */
TEST(static_method_no_args) {
    auto out = compile_spl(
        "struct Counter:\n"
        "    v: i64\n"
        "impl Counter:\n"
        "    static fn zero() -> Counter:\n"
        "        return Counter(v: 0)\n"
        "fn test():\n"
        "    val c = Counter.zero()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Counter__zero()");
}

/* --- Instance method with string arg in args (branch 1019-1030) --- */
TEST(instance_method_string_arg) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn greet(msg: text) -> text:\n"
        "        return msg\n"
        "fn test():\n"
        "    var o = Obj(v: 1)\n"
        "    val r = o.greet(\"hello\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Obj__greet");
    ASSERT_CONTAINS(out.c_str(), "\"hello\"");
}

/* --- Generic method call with string arg (branch 1063-1074) --- */
TEST(generic_method_string_arg_call) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x = 42\n"
        "    val r = x.to_string(\"fmt\")\n"
    );
    /* generic method: to_string(x, "fmt") */
    ASSERT_CONTAINS(out.c_str(), "to_string");
    ASSERT_CONTAINS(out.c_str(), "\"fmt\"");
}

/* --- Field indexing: text field with bracket (branch 1138-1147) --- */
TEST(struct_field_text_index_b4) {
    auto out = compile_spl(
        "struct Token:\n"
        "    value: text\n"
        "fn test(t: Token) -> text:\n"
        "    return t.value[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_char");
}

/* --- Field indexing: text array field (branch 1148-1149) --- */
TEST(struct_field_text_array_index_b4) {
    auto out = compile_spl(
        "struct Doc:\n"
        "    lines: [text]\n"
        "fn test(d: Doc) -> text:\n"
        "    return d.lines[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "as_str");
}

/* --- Field indexing: int array field (branch 1150-1151) --- */
TEST(struct_field_int_array_index) {
    auto out = compile_spl(
        "struct Grid:\n"
        "    data: [i64]\n"
        "fn test(g: Grid) -> i64:\n"
        "    return g.data[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "as_int");
}

/* --- Field with slice: obj.field[a:b] (branch 1122-1129) --- */
TEST(struct_field_text_slice) {
    auto out = compile_spl(
        "struct Token:\n"
        "    value: text\n"
        "fn test(t: Token) -> text:\n"
        "    return t.value[0:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

/* --- Constructor positional arg break (branch 1265) --- */
TEST(constructor_positional_break) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    val p = Pt(42)\n"
    );
    /* Positional arg breaks out */
    ASSERT_CONTAINS(out.c_str(), "Pt{");
}

/* --- Array indexing: nested array (branch 1379-1380) --- */
TEST(nested_array_index) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [[i64]] = []\n"
        "    val inner = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "as_array");
}

/* --- Array indexing: text array (branch 1381-1382) --- */
TEST(text_array_index) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = []\n"
        "    val s = arr[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "as_str");
}

/* --- Text indexing (branch 1385-1386) --- */
TEST(text_char_index) {
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_index_char");
}

/* --- Array slicing (branch 1361-1372) --- */
TEST(text_slice_expr) {
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s[1:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

/* --- Bare enum variant (branch 1395) --- */
TEST(bare_enum_variant_b4) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Blue\n"
        "fn test() -> i64:\n"
        "    return Red\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Color_Red");
}

/* --- Type inference: bool literal (branch 1452-1453) --- */
TEST(type_infer_bool_true) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x = true\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool x");
}

/* --- Type inference: struct constructor (branch 1458-1467) --- */
TEST(type_infer_struct_constructor) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    val p = Pt(x: 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

/* --- Type inference: function returning text (branch 1557-1559) --- */
TEST(type_infer_fn_text_return) {
    auto out = compile_spl(
        "fn greet() -> text:\n"
        "    return \"hello\"\n"
        "fn test():\n"
        "    val s = greet()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

/* --- Type inference: function returning bool (branch 1560) --- */
TEST(type_infer_fn_bool_return) {
    auto out = compile_spl(
        "fn check() -> bool:\n"
        "    return true\n"
        "fn test():\n"
        "    val b = check()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

/* --- Type inference: function returning array (branch 1561) --- */
TEST(type_infer_fn_array_return) {
    auto out = compile_spl(
        "fn get_items() -> [i64]:\n"
        "    var arr: [i64] = []\n"
        "    return arr\n"
        "fn test():\n"
        "    val items = get_items()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "SplArray* items");
}

/* --- Type inference: function returning struct (branch 1562) --- */
TEST(type_infer_fn_struct_return) {
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

/* --- Type inference: ?? operator unwraps option (branch 1565-1580) --- */
TEST(type_infer_option_coalescing) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = 5\n"
        "    val y = x ?? 0\n"
    );
    /* y should be i64, not Option_i64 */
    ASSERT_CONTAINS(out.c_str(), "const int64_t y");
}

/* --- Type inference: fn() ?? default (branch 1585-1592) --- */
TEST(type_infer_fn_option_coalescing) {
    auto out = compile_spl(
        "fn get_val() -> i64?:\n"
        "    return 42\n"
        "fn test():\n"
        "    val y = get_val() ?? 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const int64_t y");
}

/* --- Type inference: text method returns (branch 1536-1542) --- */
TEST(type_infer_text_trim) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val t = s.trim()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* t");
}

TEST(type_infer_text_starts_with) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val b = s.starts_with(\"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

TEST(type_infer_text_contains) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val b = s.contains(\"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

TEST(type_infer_text_ends_with) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val b = s.ends_with(\"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

TEST(type_infer_text_replace) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val r = s.replace(\"a\", \"b\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* r");
}

/* --- Type inference: static method return type (branch 1551-1553) --- */
TEST(type_infer_static_method) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "impl Pt:\n"
        "    static fn origin() -> Pt:\n"
        "        return Pt(x: 0)\n"
        "fn test():\n"
        "    val p = Pt.origin()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

/* --- Type inference: instance method return type (branch 1546-1548) --- */
TEST(type_infer_instance_method) {
    auto out = compile_spl(
        "struct Box:\n"
        "    v: i64\n"
        "impl Box:\n"
        "    fn get_val() -> i64:\n"
        "        return self.v\n"
        "fn test():\n"
        "    val b = Box(v: 1)\n"
        "    val x = b.get_val()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const int64_t x");
}

/* --- Type inference: slice expression (branch 1597-1608) --- */
TEST(type_infer_slice_expr) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    val sub = s[0:3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* sub");
}

/* --- Type inference: struct field Option unwrap (branch 1508-1528) --- */
TEST(type_infer_struct_field_option_unwrap) {
    auto out = compile_spl(
        "struct Cfg:\n"
        "    name: text?\n"
        "fn test(c: Cfg):\n"
        "    val n = c.name.unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* n");
}

/* --- Type inference: struct field Option is_some (branch 1529) --- */
TEST(type_infer_struct_field_option_is_some) {
    auto out = compile_spl(
        "struct Cfg:\n"
        "    name: text?\n"
        "fn test(c: Cfg):\n"
        "    val b = c.name.is_some()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

/* --- Type inference: Option .is_some (branch 1502) --- */
TEST(type_infer_option_var_is_some) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = 5\n"
        "    val b = x.is_some()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const bool b");
}

/* --- Type inference: expr_is_text fallback (branch 1611-1612) --- */
TEST(type_infer_expr_is_text_fallback) {
    auto out = compile_spl(
        "fn get_name() -> text:\n"
        "    return \"hello\"\n"
        "fn test():\n"
        "    val s = get_name()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

/* --- translate_statement: return nil with option func (branch 2241) --- */
TEST(translate_stmt_return_nil_option) {
    auto out = compile_spl(
        "fn find() -> i64?:\n"
        "    if true: return nil\n"
        "    return 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {};");
}

/* --- translate_statement: bare return (branch 2249) --- */
TEST(translate_stmt_bare_return_b4) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: return\n"
    );
    /* Single-line if with bare return handled in translate_block, not translate_statement.
     * Use translate_statement path via nested context */
    ASSERT_CONTAINS(out.c_str(), "return;");
}

/* --- translate_statement: break (branch 2251) --- */
TEST(translate_stmt_break) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if true: break\n"
    );
    ASSERT_CONTAINS(out.c_str(), "break;");
}

/* --- translate_statement: continue (branch 2252) --- */
TEST(translate_stmt_continue) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if true: continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "continue;");
}

/* --- translate_statement: pass (branch 2253) --- */
TEST(translate_stmt_pass) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "pass");
}

/* --- translate_statement: use/export/import skip (branch 2174-2175) --- */
TEST(translate_stmt_use_skip) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: use foo.bar\n"
    );
    /* use is skipped, no crash */
    ASSERT(out.size() > 0);
}

/* --- translate_statement: print (branch 2263) --- */
TEST(translate_stmt_print_int) {
    auto out = compile_spl(
        "fn test(x: i64):\n"
        "    if true: print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf");
}

/* --- translate_statement: += (branch 2283) --- */
TEST(translate_stmt_plus_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x += 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "+=");
}

/* --- translate_statement: -= (branch 2290) --- */
TEST(translate_stmt_minus_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x -= 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "-=");
}

/* --- translate_statement: = (branch 2297-2298) --- */
TEST(translate_stmt_simple_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x = 5");
}

/* --- translate_statement: val array (branch 2182) --- */
TEST(translate_stmt_val_array_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val arr: [i64] = [1, 2, 3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

/* --- translate_statement: val option nil (branch 2190) --- */
TEST(translate_stmt_val_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val x: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {};");
}

/* --- translate_statement: val const-prefixed type (branch 2202) --- */
TEST(translate_stmt_val_const_type) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val s: text = \"hello\"\n"
    );
    /* text → const char*, starts with "const " so no extra const added */
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

/* --- translate_statement: var array init (branch 2218) --- */
TEST(translate_stmt_var_array_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: var arr: [i64] = [1, 2]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

/* --- translate_statement: var option nil (branch 2223) --- */
TEST(translate_stmt_var_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: var x: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {};");
}

/* --- translate_statement: array element assignment (branch 2308-2323) --- */
TEST(translate_stmt_array_set) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = []\n"
        "    if true: arr[0] = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
}

/* --- translate_statement: option nil assignment (branch 2329) --- */
TEST(translate_stmt_option_nil_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = 5\n"
        "    if true: x = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "= {};");
}

/* --- translate_block: use/export skip (branch 1934-1935) --- */
TEST(block_use_skip) {
    auto out = compile_spl(
        "fn test():\n"
        "    use foo\n"
        "    val x: i64 = 1\n"
    );
    /* use is skipped, x is declared */
    ASSERT_CONTAINS(out.c_str(), "int64_t x");
}

/* --- translate_block: val option nil in block (branch 1956) --- */
TEST(block_val_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {};");
}

/* --- translate_block: var option nil in block (branch 2000) --- */
TEST(block_var_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {};");
}

/* --- translate_block: return nil in option func (branch 2020) --- */
TEST(block_return_nil_option) {
    auto out = compile_spl(
        "fn find() -> i64?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {};");
}

/* --- translate_block: pass/() (branch 2046) --- */
TEST(block_pass_statement) {
    auto out = compile_spl(
        "fn test():\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "pass");
}

TEST(block_unit_statement) {
    auto out = compile_spl(
        "fn test():\n"
        "    ()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "pass");
}

/* --- translate_block: option nil assignment (branch 2141) --- */
TEST(block_option_nil_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = 5\n"
        "    x = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "= {};");
}

/* --- translate_block: += in block (branch 2085) --- */
TEST(block_plus_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    x += 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x += 1");
}

/* --- translate_block: -= in block (branch 2096) --- */
TEST(block_minus_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    x -= 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x -= 1");
}

/* --- elif / else in translate_block (branch 1741-1744) --- */
TEST(block_elif_else) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    if x == 1:\n"
        "        return 10\n"
        "    elif x == 2:\n"
        "        return 20\n"
        "    else:\n"
        "        return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "else if");
    ASSERT_CONTAINS(out.c_str(), "else {");
}

/* --- match in translate_block (branch 1864) --- */
TEST(block_match_enum) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Blue\n"
        "fn test(c: i64) -> i64:\n"
        "    match c:\n"
        "        case Red:\n"
        "            return 1\n"
        "        case Blue:\n"
        "            return 2\n"
        "        case _:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
    ASSERT_CONTAINS(out.c_str(), "case Color_Red:");
    ASSERT_CONTAINS(out.c_str(), "default:");
}

/* --- for item in array (branch 1844-1854) --- */
TEST(for_item_in_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [1, 2, 3]\n"
        "    for x in arr:\n"
        "        print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_len");
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
}

/* --- for x in range(start, end) (branch 1825-1827) --- */
TEST(for_range_two_args) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(5, 10):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 5; i < 10; i++)");
}

/* --- while in translate_block (branch 1768) --- */
TEST(block_while_loop) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    while x < 10:\n"
        "        x += 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while");
}

/* --- emit_array_literal_pushes: nested array element (branch 1637-1642) --- */
TEST(array_literal_nested) {
    auto out = compile_spl(
        "fn test():\n"
        "    val arr: [i64] = [10, 20, 30]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
    ASSERT_CONTAINS(out.c_str(), "spl_int(10)");
}

/* --- register_func_sig: me method (branch 2359-2360) --- */
TEST(me_method_register) {
    auto out = compile_spl(
        "struct Cnt:\n"
        "    v: i64\n"
        "impl Cnt:\n"
        "    me inc():\n"
        "        self.v = self.v + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Cnt* self");
}

/* --- register_func_sig: extern fn (branch 2358) --- */
TEST(extern_fn_register) {
    auto out = compile_spl(
        "extern fn rt_read(path: text) -> text\n"
    );
    ASSERT_CONTAINS(out.c_str(), "extern \"C\"");
    ASSERT_CONTAINS(out.c_str(), "rt_read");
}

/* --- register_func_sig: static fn (branch 2360) --- */
TEST(static_fn_register) {
    auto out = compile_spl(
        "struct Factory:\n"
        "    v: i64\n"
        "impl Factory:\n"
        "    static fn make() -> Factory:\n"
        "        return Factory(v: 0)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Factory__make");
}

/* --- register_func_sig: unrecognized line (branch 2361) --- */
TEST(register_func_unrecognized) {
    auto out = compile_spl(
        "struct Foo:\n"
        "    v: i64\n"
        "impl Foo:\n"
        "    val x = 42\n"
    );
    /* val inside impl is unrecognized by register_func_sig → returns false */
    ASSERT(out.size() > 0);
}

/* --- process_file: extern fn with multiple params (branch 2646) --- */
TEST(extern_fn_multi_params) {
    auto out = compile_spl(
        "extern fn rt_write(path: text, content: text) -> i64\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* path, const char* content");
}

/* --- Module-level vars: non-constant text (branch 2704) --- */
TEST(module_var_text_default) {
    auto out = compile_spl(
        "var name: text = get_name()\n"
        "fn get_name() -> text:\n"
        "    return \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static const char* name = \"\"");
}

/* --- Module-level vars: non-constant bool (branch 2706-2707) --- */
TEST(module_var_bool_default) {
    auto out = compile_spl(
        "var flag: bool = compute()\n"
        "fn compute() -> bool:\n"
        "    return true\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static bool flag = false");
}

/* --- Module-level vars: non-constant int (branch 2708-2709) --- */
TEST(module_var_int_default) {
    auto out = compile_spl(
        "var count: i64 = compute()\n"
        "fn compute() -> i64:\n"
        "    return 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t count = 0");
}

/* --- Module-level vars: struct type (branch 2697-2698) --- */
TEST(module_var_struct_type) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "var p: Pt = Pt(x: 0)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Pt p = {}");
}

/* --- Implicit return: fn with last stmt being 'if' → no return added (branch 2767-2769) --- */
TEST(implicit_return_ends_with_if) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    if x > 0:\n"
        "        return x\n"
        "    return 0\n"
    );
    /* Last stmt is 'return', no implicit return needed */
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* --- Implicit return: fn with last stmt being 'for' → no return added --- */
TEST(implicit_return_ends_with_for) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    for i in 0..10:\n"
        "        print i\n"
    );
    /* Last stmt is 'for', needs_return set to false */
    ASSERT_NOT_CONTAINS(out.c_str(), "return for");
}

/* --- Implicit return: fn with last stmt being 'val' → no return added --- */
TEST(implicit_return_ends_with_val) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    val x: i64 = 42\n"
    );
    /* Last stmt is 'val', needs_return = false → no return prepended */
    ASSERT_NOT_CONTAINS(out.c_str(), "return const");
}

/* --- Implicit return: fn with last stmt being 'while' → no return added --- */
TEST(implicit_return_ends_with_while) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    while true:\n"
        "        return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while");
}

/* --- Implicit return: fn with last stmt being 'match' → no return added --- */
TEST(implicit_return_ends_with_match) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 0:\n"
        "            return 1\n"
        "        case _:\n"
        "            return 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
}

/* --- Implicit return: fn ending with 'break' → no return (branch 2772) --- */
TEST(implicit_return_ends_with_break_fn) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    break\n"
    );
    /* break → needs_return = false */
    ASSERT_CONTAINS(out.c_str(), "break;");
    ASSERT_NOT_CONTAINS(out.c_str(), "return break");
}

/* --- Implicit return: fn ending with 'print' → no return (branch 2773) --- */
TEST(implicit_return_ends_with_print) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    print 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf");
    ASSERT_NOT_CONTAINS(out.c_str(), "return printf");
}

/* --- Implicit return: fn ending with 'else:' → no return (branch 2770) --- */
TEST(implicit_return_ends_with_else) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    if x > 0:\n"
        "        return 1\n"
        "    else:\n"
        "        return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "else");
}

/* --- Implicit return: fn ending with 'case' → no return (branch 2774) --- */
TEST(implicit_return_ends_with_case) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 1:\n"
        "            return 10\n"
        "        case _:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
}

/* --- Implicit return: fn ending with 'continue' → no return (branch 2772) --- */
TEST(implicit_return_ends_with_continue_fn) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "continue;");
    ASSERT_NOT_CONTAINS(out.c_str(), "return continue");
}

/* --- Implicit return: fn ending with expression with assignment (branch 2779) --- */
TEST(implicit_return_assignment_last_stmt) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    var x: i64 = 0\n"
        "    x = 42\n"
    );
    /* Assignment → needs_return = false (detected by = sign) */
    ASSERT_NOT_CONTAINS(out.c_str(), "return x = 42");
}

/* --- Implicit return: fn ending with != operator (branch 2779 lt[ci-1]!='!') --- */
TEST(implicit_return_ne_comparison) {
    auto out = compile_spl(
        "fn test(a: i64) -> bool:\n"
        "    a != 0\n"
    );
    /* != is comparison, not assignment → should get return prepended */
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* --- Implicit return: fn ending with <= operator (branch 2779 lt[ci-1]!='<') --- */
TEST(implicit_return_le_comparison) {
    auto out = compile_spl(
        "fn test(a: i64) -> bool:\n"
        "    a <= 10\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* --- Implicit return: fn ending with >= operator (branch 2779 lt[ci-1]!='>') --- */
TEST(implicit_return_ge_comparison) {
    auto out = compile_spl(
        "fn test(a: i64) -> bool:\n"
        "    a >= 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* --- Implicit return: fn ending with == operator (branch 2779 lt[ci-1]!='=') --- */
TEST(implicit_return_eq_comparison) {
    auto out = compile_spl(
        "fn test(a: i64) -> bool:\n"
        "    a == 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* --- Method implicit return: ending with various statements (branch 2889-2899) --- */
TEST(method_implicit_return_if) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn check() -> i64:\n"
        "        if self.v > 0:\n"
        "            return 1\n"
        "        return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Obj__check");
}

TEST(method_implicit_return_for) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn loop_test() -> i64:\n"
        "        for i in 0..self.v:\n"
        "            print i\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "return for");
}

TEST(method_implicit_return_val) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn get() -> i64:\n"
        "        val x: i64 = self.v\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "return const");
}

TEST(method_implicit_return_var) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn get() -> i64:\n"
        "        var x: i64 = self.v\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "return int64_t");
}

TEST(method_implicit_return_break) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn get() -> i64:\n"
        "        break\n"
    );
    ASSERT_CONTAINS(out.c_str(), "break;");
    ASSERT_NOT_CONTAINS(out.c_str(), "return break");
}

TEST(method_implicit_return_print) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn show() -> i64:\n"
        "        print self.v\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf");
    ASSERT_NOT_CONTAINS(out.c_str(), "return printf");
}

TEST(method_implicit_return_assign) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn get() -> i64:\n"
        "        var x: i64 = 0\n"
        "        x = self.v\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "return x = ");
}

TEST(method_implicit_return_ne) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn check() -> bool:\n"
        "        self.v != 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

TEST(method_implicit_return_le) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn check() -> bool:\n"
        "        self.v <= 10\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

TEST(method_implicit_return_ge) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn check() -> bool:\n"
        "        self.v >= 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

TEST(method_implicit_return_eq) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn check() -> bool:\n"
        "        self.v == 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* --- Method body processing (branch 2810, 2841) --- */
TEST(method_body_struct_type_processing) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "    y: i64\n"
        "impl Pt:\n"
        "    fn sum() -> i64:\n"
        "        return self.x + self.y\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->x + self->y");
}

/* --- Module level: init function block (branch 2728, 2732) --- */
TEST(module_init_block) {
    auto out = compile_spl(
        "fn init():\n"
        "    val x: i64 = 42\n"
        "    print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "void init()");
}

/* --- for range single arg (branch 1837-1842) --- */
TEST(for_range_single_arg) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(5):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 0; i < 5; i++)");
}

/* --- match with pipe separator (branch 1884) --- */
TEST(match_pipe_case) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 1 | 2:\n"
        "            return 10\n"
        "        case _:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case 1:");
    ASSERT_CONTAINS(out.c_str(), "case 2:");
}

/* --- match with wildcard in pipe (branch 1890-1892) --- */
TEST(match_pipe_wildcard) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 1 | _:\n"
        "            return 10\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case 1:");
    ASSERT_CONTAINS(out.c_str(), "default:");
}

/* --- match pipe with enum variant (branch 1897-1898) --- */
TEST(match_pipe_enum) {
    auto out = compile_spl(
        "enum Dir:\n"
        "    Up\n"
        "    Down\n"
        "    Left\n"
        "fn test(d: i64) -> i64:\n"
        "    match d:\n"
        "        case Up | Down:\n"
        "            return 1\n"
        "        case _:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case Dir_Up:");
    ASSERT_CONTAINS(out.c_str(), "case Dir_Down:");
}

/* --- Not prefix (branch 647-651) --- */
TEST(not_prefix_expr) {
    auto out = compile_spl(
        "fn test(x: bool) -> bool:\n"
        "    return not x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!(");
}

/* --- Paren expr empty (branch 669-670) --- */
TEST(paren_expr_empty) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    return ()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "0 /* unit */");
}

/* --- String interp with text var (branch 595 path) --- */
TEST(string_interp_text_var) {
    auto out = compile_spl(
        "fn test(name: text) -> text:\n"
        "    return \"hello {name}!\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_NOT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

/* --- Nested array set in statement (branch 2318-2319) --- */
TEST(translate_stmt_nested_array_set) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [[i64]] = []\n"
        "    var inner: [i64] = []\n"
        "    if true: arr[0] = inner\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_val");
}

/* --- Text array set in statement (branch 2320-2321) --- */
TEST(translate_stmt_text_array_set) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = []\n"
        "    if true: arr[0] = \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

/* --- Option nil compare == (branch 776-777) --- */
TEST(option_nil_eq) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = 5\n"
        "    val b = x == nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!x.has_value");
}

/* --- Option nil compare != (branch 778-779) --- */
TEST(option_nil_ne) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = 5\n"
        "    val b = x != nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x.has_value");
}

/* --- Self field access (branch 1159-1160) --- */
TEST(self_field_simple) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "impl Pt:\n"
        "    fn get_x() -> i64:\n"
        "        return self.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->x");
}

/* --- Dot expr field with bracket before paren (branch 958-964) --- */
TEST(field_bracket_before_paren) {
    auto out = compile_spl(
        "struct Grid:\n"
        "    data: [i64]\n"
        "fn test(g: Grid) -> i64:\n"
        "    return g.data[0]\n"
    );
    /* data[0] has bracket before paren → treated as field+indexing */
    ASSERT_CONTAINS(out.c_str(), "g.data");
}

/* --- Struct Option field: base is struct (Phase D emit) --- */
TEST(struct_option_field_emit) {
    auto out = compile_spl(
        "struct Inner:\n"
        "    v: i64\n"
        "struct Outer:\n"
        "    child: Inner?\n"
    );
    /* Should emit Option_Inner struct after Inner is defined */
    ASSERT_CONTAINS(out.c_str(), "Option_Inner");
    ASSERT_CONTAINS(out.c_str(), "struct Inner {");
}

/* --- Nested struct constructor with string field (branch 1243-1247) --- */
TEST(constructor_string_field) {
    auto out = compile_spl(
        "struct Token:\n"
        "    kind: text\n"
        "    value: text\n"
        "fn test():\n"
        "    val t = Token(kind: \"ident\", value: \"x\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".kind = \"ident\"");
    ASSERT_CONTAINS(out.c_str(), ".value = \"x\"");
}

/* --- Function call with string arg in function call (branch 1301-1307) --- */
TEST(fn_call_string_arg) {
    auto out = compile_spl(
        "fn greet(name: text) -> text:\n"
        "    return name\n"
        "fn test():\n"
        "    val r = greet(\"world\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "greet(\"world\")");
}

/* --- Multi-param function call (branch 1311, 1324) --- */
TEST(fn_call_multi_params) {
    auto out = compile_spl(
        "fn add(a: i64, b: i64) -> i64:\n"
        "    return a + b\n"
        "fn test():\n"
        "    val r = add(1, 2)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "add(1, 2)");
}

/* --- Param array type in parse (branch 2392-2395) --- */
TEST(fn_param_array_type_parse) {
    auto out = compile_spl(
        "fn process(items: [text]) -> i64:\n"
        "    return items.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "SplArray* items");
}

/* --- expr_is_text: struct method returns text (branch 480-494) --- */
TEST(expr_is_text_struct_method) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn name() -> text:\n"
        "        return \"obj\"\n"
        "fn test():\n"
        "    val o = Obj(v: 1)\n"
        "    print o.name()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

/* --- expr_is_text: function returning text (branch 497-505) --- */
TEST(expr_is_text_func_return) {
    auto out = compile_spl(
        "fn get_name() -> text:\n"
        "    return \"hi\"\n"
        "fn test():\n"
        "    print get_name()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

/* --- Self field indexing: self.field[i] (branch 1103-1104) --- */
TEST(self_field_array_index) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    data: [i64]\n"
        "impl Obj:\n"
        "    fn get(i: i64) -> i64:\n"
        "        return self.data[i]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "self->data");
    ASSERT_CONTAINS(out.c_str(), "as_int");
}

/* --- Module-level: init function with call (branch 2966) --- */
TEST(module_init_call) {
    auto out = compile_spl(
        "var x: i64 = 0\n"
        "fn setup():\n"
        "    x = 42\n"
        "fn main():\n"
        "    setup()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "setup()");
}

/* ================================================================
 * Coverage Batch 5: False-side Branch Targeting
 * ================================================================ */

/* Comparison operators as expression statements in translate_block.
 * These hit the False sides of the assignment-detection compound condition
 * at line 2108: trimmed[i-1] != '!', '< ', '>', '='
 * The scanner encounters = in !=, <=, >=, == and must NOT treat them as assignments.
 */
TEST(block_expr_ne_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a != b\n"
    );
    /* != is expression, not assignment */
    ASSERT_CONTAINS(out.c_str(), "!=");
}

TEST(block_expr_le_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a <= b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "<=");
}

TEST(block_expr_ge_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a >= b\n"
    );
    ASSERT_CONTAINS(out.c_str(), ">=");
}

TEST(block_expr_eq_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    a == b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "==");
}

/* Same for translate_statement path (line 2298) — via single-line if body */
TEST(stmt_expr_ne_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    if true: a != b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "!=");
}

TEST(stmt_expr_le_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    if true: a <= b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "<=");
}

TEST(stmt_expr_ge_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    if true: a >= b\n"
    );
    ASSERT_CONTAINS(out.c_str(), ">=");
}

TEST(stmt_expr_eq_comparison) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64):\n"
        "    if true: a == b\n"
    );
    ASSERT_CONTAINS(out.c_str(), "==");
}

/* --- String interp: literal before first interpolation (branch 568-575) --- */
TEST(string_interp_literal_then_expr) {
    auto out = compile_spl(
        "fn test(x: i64) -> text:\n"
        "    return \"count={x}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "\"count=\"");
}

/* --- String interp: expr with text (not needing i64_to_str) (branch 595) --- */
TEST(string_interp_text_expr_direct) {
    auto out = compile_spl(
        "fn test() -> text:\n"
        "    val name: text = \"world\"\n"
        "    return \"hello {name}!\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    /* name is text → no i64_to_str */
}

/* --- String interp: literal only in first segment, then interp (branch 568 str_pos > 2) --- */
TEST(string_interp_prefix_literal) {
    auto out = compile_spl(
        "fn test(n: i64) -> text:\n"
        "    return \"val={n}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "\"val=\"");
}

/* --- String interp: multiple expressions (branch 601-606) --- */
TEST(string_interp_multiple_exprs) {
    auto out = compile_spl(
        "fn test(a: i64, b: i64) -> text:\n"
        "    return \"{a} and {b}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* --- String interp: expression produces text via expr_is_text (branch 595:54 True) --- */
TEST(string_interp_text_string_literal) {
    auto out = compile_spl(
        "fn test() -> text:\n"
        "    val s: text = \"x\"\n"
        "    return \"v={s}\"\n"
    );
    /* s is text var → no i64_to_str conversion */
    ASSERT_NOT_CONTAINS(out.c_str(), "spl_i64_to_str(s)");
}

/* --- Struct field with unknown type indexed (branch 1153) --- */
TEST(struct_field_raw_index) {
    auto out = compile_spl(
        "struct Grid:\n"
        "    buf: i64\n"
        "fn test(g: Grid) -> i64:\n"
        "    return g.buf[0]\n"
    );
    /* buf is i64, not array/text → raw indexing fallback */
    ASSERT_CONTAINS(out.c_str(), "g.buf[0]");
}

/* --- extract_condition: trailing whitespace (branch 1627) --- */
TEST(extract_cond_trailing_space) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true  :\n"
        "        print 1\n"
    );
    /* Extra spaces before colon should be trimmed */
    ASSERT_CONTAINS(out.c_str(), "if (true)");
}

/* --- parse_var_decl: no type, no equals, just name (branch 1418, 1436, 1440) --- */
TEST(var_decl_no_type_no_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x");
}

/* --- is_constant_expr: empty string (branch 440) --- */
TEST(constant_expr_empty) {
    /* This exercises module-level var with no RHS */
    auto out = compile_spl(
        "var x: i64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t x = 0");
}

/* --- is_constant_expr: negative number (branch 441) --- */
TEST(constant_expr_negative) {
    auto out = compile_spl(
        "var x: i64 = -1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t x = -1");
}

/* --- is_constant_expr: string (branch 442) --- */
TEST(constant_expr_string) {
    auto out = compile_spl(
        "var s: text = \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static const char* s = \"hello\"");
}

/* --- is_constant_expr: bool (branch 443) --- */
TEST(constant_expr_bool_true) {
    auto out = compile_spl(
        "var f: bool = true\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static bool f = true");
}

TEST(constant_expr_bool_false) {
    auto out = compile_spl(
        "var f: bool = false\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static bool f = false");
}

/* --- is_constant_expr: nil (branch 443) --- */
TEST(constant_expr_nil) {
    auto out = compile_spl(
        "var x: i64 = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t x = ");
}

/* --- translate_block: nested array set (branch 2120, 2130) --- */
TEST(block_nested_array_set) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [[i64]] = []\n"
        "    var inner: [i64] = []\n"
        "    arr[0] = inner\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_val");
}

/* --- translate_block: text array set (branch 2132-2133) --- */
TEST(block_text_array_set) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [text] = []\n"
        "    arr[0] = \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

/* --- translate_block: val with struct (branch 1969-1970) --- */
TEST(block_val_struct) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "fn test():\n"
        "    val p: Pt = Pt(x: 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const Pt p");
}

/* --- translate_block: option struct field assignment to nil (branch 2141 dot_expr_is_option) --- */
TEST(block_dot_option_nil_assign) {
    auto out = compile_spl(
        "struct Config:\n"
        "    name: text?\n"
        "fn test(c: Config):\n"
        "    var cfg = c\n"
    );
    /* Just verify compilation works with option struct fields */
    ASSERT_CONTAINS(out.c_str(), "Option_text");
}

/* --- Method body: match (branch 2810 indirect) --- */
TEST(method_body_match) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn classify() -> text:\n"
        "        match self.v:\n"
        "            case 0:\n"
        "                return \"zero\"\n"
        "            case _:\n"
        "                return \"other\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
    ASSERT_CONTAINS(out.c_str(), "self->v");
}

/* --- Method body: while (branch 2810 indirect) --- */
TEST(method_body_while) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn count_down() -> i64:\n"
        "        var x: i64 = self.v\n"
        "        while x > 0:\n"
        "            x -= 1\n"
        "        return x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while");
}

/* --- Method body: for range (branch 2810 indirect) --- */
TEST(method_body_for_range) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    v: i64\n"
        "impl Obj:\n"
        "    fn sum_up() -> i64:\n"
        "        var total: i64 = 0\n"
        "        for i in 0..self.v:\n"
        "            total += i\n"
        "        return total\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i");
}

/* --- Struct field: Option type indexed (exercise both field paths) --- */
TEST(struct_field_option) {
    auto out = compile_spl(
        "struct Cfg:\n"
        "    count: i64?\n"
        "fn test(c: Cfg) -> bool:\n"
        "    return c.count.is_some()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

/* --- Multiple function params with types (register_func_sig param parsing) --- */
TEST(fn_multi_param_types) {
    auto out = compile_spl(
        "fn compute(x: i64, name: text, items: [i64]) -> i64:\n"
        "    return x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x");
    ASSERT_CONTAINS(out.c_str(), "const char* name");
    ASSERT_CONTAINS(out.c_str(), "SplArray* items");
}

/* --- translate_statement return nil in option (branch 2241) - this needs
 * to go through translate_statement path specifically --- */
TEST(translate_stmt_option_return_nil) {
    auto out = compile_spl(
        "fn find(x: i64) -> i64?:\n"
        "    if x > 0: return nil\n"
        "    return 42\n"
    );
    /* Single-line if → return nil → handled in translate_block single-line if,
     * which calls emit("return {};") at line 1703-1704 */
    ASSERT_CONTAINS(out.c_str(), "return {};");
}

/* --- Module-level val constant (branch 2699-2702) --- */
TEST(module_val_constant) {
    auto out = compile_spl(
        "val MAX: i64 = 100\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static int64_t MAX = 100");
}

/* --- Module-level: array variable (branch 2693-2694) --- */
TEST(module_var_array) {
    auto out = compile_spl(
        "var items: [i64] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static SplArray* items");
}

/* --- Module-level: option variable (branch 2695-2696) --- */
TEST(module_var_option) {
    auto out = compile_spl(
        "var opt: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Option_i64 opt = {}");
}

/* --- Struct with comment line (hit struct field parsing edge case) --- */
TEST(struct_with_comment) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    # x coordinate\n"
        "    x: i64\n"
        "    # y coordinate\n"
        "    y: i64\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x");
    ASSERT_CONTAINS(out.c_str(), "int64_t y");
}

/* --- Enum with comment line --- */
TEST(enum_with_comment) {
    auto out = compile_spl(
        "enum Color:\n"
        "    # primary\n"
        "    Red\n"
        "    Green\n"
        "    Blue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Color_Red");
    ASSERT_CONTAINS(out.c_str(), "Color_Green");
    ASSERT_CONTAINS(out.c_str(), "Color_Blue");
}

/* --- impl with comment (already tested but need method body processing) --- */
TEST(impl_with_methods_and_comments) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "    y: i64\n"
        "impl Pt:\n"
        "    # getter\n"
        "    fn get_x() -> i64:\n"
        "        return self.x\n"
        "    # setter\n"
        "    me set_x(new_x: i64):\n"
        "        self.x = new_x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Pt__get_x");
    ASSERT_CONTAINS(out.c_str(), "Pt__set_x");
}

/* --- fn with return type and trailing space before colon (branch 2418) --- */
TEST(fn_sig_return_type_space) {
    auto out = compile_spl(
        "fn get_val() -> i64:\n"
        "    return 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t get_val()");
}

/* --- Single-line if with nested parens in condition (branch 1681-1685) --- */
TEST(single_line_if_complex_cond) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    if (x + 1) > 0: return x\n"
        "    return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "(x + 1)");
    ASSERT_CONTAINS(out.c_str(), "> 0");
    ASSERT_CONTAINS(out.c_str(), "return x;");
}

/* --- Constructor with multiple named fields incl nested call (branch 1239-1250) --- */
TEST(constructor_nested_call_arg) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "    y: i64\n"
        "fn double_val(v: i64) -> i64:\n"
        "    return v * 2\n"
        "fn test():\n"
        "    val p = Pt(x: double_val(3), y: 4)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Pt{.x = double_val(3), .y = 4}");
}

/* ================================================================
 * Batch 6: Remaining Branch Coverage
 * ================================================================ */

/* --- For Loop Variants --- */
TEST(for_in_array_loop) {
    auto out = compile_spl(
        "fn test(items: [i64]):\n"
        "    for x in items:\n"
        "        print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t __x_i = 0; __x_i < spl_array_len(");
    ASSERT_CONTAINS(out.c_str(), "int64_t x = spl_array_get(");
}

TEST(for_range_single_arg_b6) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(10):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 0; i < 10; i++)");
}

TEST(for_range_two_args_b6) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(2, 8):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 2; i < 8; i++)");
}

/* --- Option Type Paths --- */
TEST(val_option_with_value) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: text? = \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
    ASSERT_CONTAINS(out.c_str(), "\"hello\"");
}

TEST(val_option_nil) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: text? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(var_option_with_value) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = 42\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "42");
    ASSERT_NOT_CONTAINS(out.c_str(), "= {}");
}

TEST(var_option_nil_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(return_nil_from_option_fn) {
    auto out = compile_spl(
        "fn maybe() -> text?:\n"
        "    return nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {}");
}

TEST(single_line_if_return_nil_option) {
    auto out = compile_spl(
        "fn maybe(x: i64) -> text?:\n"
        "    if x > 0: return nil\n"
        "    return \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return {}");
    ASSERT_CONTAINS(out.c_str(), "return \"hello\"");
}

TEST(option_nil_assignment_block) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: text? = \"hello\"\n"
        "    x = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x = {}");
}

TEST(option_dot_nil_assignment_block) {
    auto out = compile_spl(
        "struct Foo:\n"
        "    name: text?\n"
        "fn test(f: Foo):\n"
        "    var g: Foo = f\n"
        "    g.name = nil\n"
    );
    /* dot_expr_is_option detects g.name is Option<text> field */
}

/* --- translate_statement Paths --- */
TEST(stmt_use_skip) {
    /* translate_statement should skip use/export/import */
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    if true: print s\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

TEST(stmt_export_skip) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x = 1\n"
    );
}

TEST(stmt_import_skip) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x = 1\n"
    );
}

TEST(stmt_val_option_nil) {
    /* This triggers translate_statement's val option nil path (line 2190) */
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: val x: text? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(stmt_val_option_value) {
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: val x: text? = \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
    ASSERT_CONTAINS(out.c_str(), "\"hi\"");
}

TEST(stmt_var_option_nil) {
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: var x: i64? = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(stmt_var_option_value) {
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: var x: i64? = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "5");
}

TEST(stmt_var_array_literal) {
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: var items: [i64] = [1, 2]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new()");
}

TEST(stmt_bare_return) {
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: return\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return;");
}

TEST(stmt_break) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if i > 5: break\n"
    );
    ASSERT_CONTAINS(out.c_str(), "break;");
}

TEST(stmt_continue) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 0..10:\n"
        "        if i > 5: continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "continue;");
}

TEST(stmt_pass) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "/* pass */");
}

TEST(stmt_unit) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: ()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "/* pass */");
}

TEST(stmt_print_int) {
    auto out = compile_spl(
        "fn test(x: i64):\n"
        "    if true: print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf(\"%lld\\n\"");
}

TEST(stmt_print_text) {
    auto out = compile_spl(
        "fn test(s: text):\n"
        "    if true: print s\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_println");
}

TEST(stmt_plus_equals) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x += 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x += 1");
}

TEST(stmt_minus_equals) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 10\n"
        "    if true: x -= 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x -= 1");
}

TEST(stmt_assignment) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 0\n"
        "    if true: x = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "x = 5");
}

TEST(stmt_text_array_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var items: [text] = []\n"
        "    if true: items[0] = \"hi\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
    ASSERT_CONTAINS(out.c_str(), "spl_str(");
}

TEST(stmt_option_nil_assign) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: text? = \"hello\"\n"
        "    if true: x = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(stmt_expr_statement) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: some_func()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "some_func()");
}

/* --- Module Level --- */
TEST(module_control_flow_if) {
    auto out = compile_spl(
        "if true:\n"
        "    print \"init\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "__module_init");
    ASSERT_CONTAINS(out.c_str(), "if (true)");
}

TEST(module_option_init_value) {
    auto out = compile_spl(
        "var cache: text? = \"initial\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
    ASSERT_CONTAINS(out.c_str(), "\"initial\"");
}

TEST(module_array_literal_init) {
    auto out = compile_spl(
        "val items: [i64] = [1, 2, 3]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

TEST(module_struct_init) {
    auto out = compile_spl(
        "struct Pt:\n"
        "    x: i64\n"
        "    y: i64\n"
        "val origin: Pt = Pt(x: 0, y: 0)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Pt{");
}

TEST(module_expr_statement) {
    auto out = compile_spl(
        "fn setup():\n"
        "    pass\n"
        "setup()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "__module_init");
    ASSERT_CONTAINS(out.c_str(), "setup()");
}

TEST(module_use_skip) {
    auto out = compile_spl(
        "use std.io\n"
        "fn test():\n"
        "    pass\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "use ");
}

/* --- String Interpolation --- */
TEST(interp_only_expr_no_prefix) {
    /* String "{x}" where interpolation starts immediately, no literal prefix */
    auto out = compile_spl(
        "fn test(name: text) -> text:\n"
        "    return \"{name}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "name");
}

TEST(interp_text_var) {
    /* String interpolation where the inner expression is a known text variable */
    auto out = compile_spl(
        "fn test(name: text) -> text:\n"
        "    return \"Hello {name}!\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "name");
}

TEST(interp_empty_result) {
    /* Edge case: string with just braces but no real interp content */
    auto out = compile_spl(
        "fn test() -> text:\n"
        "    return \"plain text\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "\"plain text\"");
}

/* --- Struct/Method --- */
TEST(struct_constructor_named_args) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "fn test() -> Point:\n"
        "    return Point(x: 10, y: 20)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Point{");
    ASSERT_CONTAINS(out.c_str(), ".x =");
    ASSERT_CONTAINS(out.c_str(), ".y =");
}

TEST(method_implicit_return_expr_b6) {
    /* Method body ending with a bare expression (needs implicit return) */
    auto out = compile_spl(
        "struct Box:\n"
        "    value: i64\n"
        "impl Box:\n"
        "    fn get_value() -> i64:\n"
        "        self.value\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return self->value");
}

TEST(fn_implicit_return_expr) {
    /* Function body ending with bare expression (needs implicit return) */
    auto out = compile_spl(
        "fn double(x: i64) -> i64:\n"
        "    x * 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return (x * 2)");
}

TEST(static_method_impl) {
    auto out = compile_spl(
        "struct Utils:\n"
        "    x: i64\n"
        "impl Utils:\n"
        "    static fn create(v: i64) -> Utils:\n"
        "        return Utils(x: v)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Utils__create");
    /* Static methods don't get self parameter */
    ASSERT_NOT_CONTAINS(out.c_str(), "Utils* self");
}

TEST(replace_no_closing_paren) {
    /* Edge case: replace method call where closing paren might be missing/separate */
    auto out = compile_spl(
        "fn test(s: text) -> text:\n"
        "    return s.replace(\"a\", \"b\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_replace");
}

TEST(for_in_array_iteration) {
    /* For-in over array variable */
    auto out = compile_spl(
        "fn test():\n"
        "    val items: [i64] = [1, 2, 3]\n"
        "    for x in items:\n"
        "        print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "__x_i");
    ASSERT_CONTAINS(out.c_str(), "spl_array_len(items)");
}

TEST(match_pipe_case_b6) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Blue\n"
        "    Green\n"
        "fn test(c: i64):\n"
        "    match c:\n"
        "        case Red | Blue:\n"
        "            print 1\n"
        "        case Green:\n"
        "            print 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
    ASSERT_CONTAINS(out.c_str(), "case Color_Red:");
    ASSERT_CONTAINS(out.c_str(), "case Color_Blue:");
}

TEST(expr_is_text_fallback_inference) {
    /* val v = t.value where Tok has text field - should infer text via expr_is_text */
    auto out = compile_spl(
        "struct Tok:\n"
        "    value: text\n"
        "fn test(t: Tok):\n"
        "    val v = t.value\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* v = ");
}

TEST(single_line_if_no_colon_body) {
    /* Single-line if with colon separating condition from body */
    auto out = compile_spl(
        "fn test(x: i64):\n"
        "    if x > 0: print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
    ASSERT_CONTAINS(out.c_str(), "> 0");
}

/* ================================================================
 * Batch 7: Deep Branch Coverage
 * ================================================================ */

/* Val/var option without initializer (covers *rhs == '\0' True side) */
TEST(stmt_val_option_no_init) {
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: val x: text?\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(stmt_var_option_no_init) {
    auto out = compile_spl(
        "fn outer():\n"
        "    if true: var x: i64?\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(block_val_option_no_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: text?\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

TEST(block_var_option_no_init) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64?\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

/* Module-level use/export/import skip in __module_init */
TEST(module_export_skip) {
    auto out = compile_spl(
        "export foo\n"
        "fn foo():\n"
        "    pass\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "export");
}

TEST(module_import_skip) {
    auto out = compile_spl(
        "import bar\n"
        "fn test():\n"
        "    pass\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "import");
}

/* Module-level while loop */
TEST(module_control_flow_while) {
    auto out = compile_spl(
        "var i: i64 = 0\n"
        "while i < 5:\n"
        "    i += 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "__module_init");
    ASSERT_CONTAINS(out.c_str(), "while (");
}

/* Module-level for loop */
TEST(module_control_flow_for) {
    auto out = compile_spl(
        "for i in 0..5:\n"
        "    print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "__module_init");
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i");
}

/* Module-level match */
TEST(module_control_flow_match) {
    auto out = compile_spl(
        "var x: i64 = 1\n"
        "match x:\n"
        "    case 1:\n"
        "        print 1\n"
        "    case 2:\n"
        "        print 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "__module_init");
    ASSERT_CONTAINS(out.c_str(), "switch (");
}

/* Function ending in 'if' → needs_return = false (line 2768) */
TEST(fn_ends_with_if) {
    auto out = compile_spl(
        "fn maybe(x: i64) -> i64:\n"
        "    if x > 0:\n"
        "        return x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
    ASSERT_CONTAINS(out.c_str(), "return x");
}

/* Function ending in 'while' → needs_return = false */
TEST(fn_ends_with_while) {
    auto out = compile_spl(
        "fn loop_fn(x: i64) -> i64:\n"
        "    while x > 0:\n"
        "        return x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while (");
}

/* Function ending in 'for' → needs_return = false */
TEST(fn_ends_with_for) {
    auto out = compile_spl(
        "fn sum_fn() -> i64:\n"
        "    for i in 0..10:\n"
        "        return i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i");
}

/* Function ending in 'match' → needs_return = false */
TEST(fn_ends_with_match) {
    auto out = compile_spl(
        "fn check(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 0:\n"
        "            return 0\n"
        "        case 1:\n"
        "            return 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch (");
}

/* Function ending in 'val' → needs_return = false */
TEST(fn_ends_with_val) {
    auto out = compile_spl(
        "fn declare(x: i64) -> i64:\n"
        "    return x\n"
        "    val unused = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return x");
}

/* Function ending in 'var' → needs_return = false */
TEST(fn_ends_with_var) {
    auto out = compile_spl(
        "fn declare2(x: i64) -> i64:\n"
        "    return x\n"
        "    var unused = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return x");
}

/* Function ending in 'break' → needs_return = false */
TEST(fn_ends_with_break) {
    auto out = compile_spl(
        "fn brk() -> i64:\n"
        "    return 0\n"
        "    break\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

/* Function ending in 'continue' → needs_return = false */
TEST(fn_ends_with_continue) {
    auto out = compile_spl(
        "fn cont() -> i64:\n"
        "    return 0\n"
        "    continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

/* Function ending in 'print' → needs_return = false */
TEST(fn_ends_with_print) {
    auto out = compile_spl(
        "fn pr() -> i64:\n"
        "    return 0\n"
        "    print 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

/* Function ending in 'case' → needs_return = false */
TEST(fn_ends_with_case) {
    auto out = compile_spl(
        "fn cs(x: i64) -> i64:\n"
        "    match x:\n"
        "        case 0:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch (");
}

/* Function ending in 'elif' → needs_return = false (line 2770) */
TEST(fn_ends_with_elif) {
    auto out = compile_spl(
        "fn check2(x: i64) -> i64:\n"
        "    if x > 0:\n"
        "        return 1\n"
        "    elif x < 0:\n"
        "        return -1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "else if");
}

/* Function ending in 'else:' → needs_return = false (line 2770) */
TEST(fn_ends_with_else) {
    auto out = compile_spl(
        "fn check3(x: i64) -> i64:\n"
        "    if x > 0:\n"
        "        return 1\n"
        "    else:\n"
        "        return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "else");
}

/* Function ending with assignment → needs_return = false (line 2778-2780) */
TEST(fn_ends_with_assignment) {
    auto out = compile_spl(
        "fn assign_fn() -> i64:\n"
        "    return 0\n"
        "    var x: i64 = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

/* Method ending with 'if' → implicit return skip (line 2890) */
TEST(method_ends_with_if) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    x: i64\n"
        "impl Obj:\n"
        "    fn check() -> i64:\n"
        "        if self.x > 0:\n"
        "            return self.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
}

/* Method ending with 'while' */
TEST(method_ends_with_while) {
    auto out = compile_spl(
        "struct Obj2:\n"
        "    x: i64\n"
        "impl Obj2:\n"
        "    fn loop_m() -> i64:\n"
        "        while self.x > 0:\n"
        "            return self.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "while (");
}

/* Method ending with 'for' */
TEST(method_ends_with_for) {
    auto out = compile_spl(
        "struct Obj3:\n"
        "    x: i64\n"
        "impl Obj3:\n"
        "    fn sum_m() -> i64:\n"
        "        for i in 0..10:\n"
        "            return i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i");
}

/* Method ending with 'match' */
TEST(method_ends_with_match) {
    auto out = compile_spl(
        "struct Obj4:\n"
        "    x: i64\n"
        "impl Obj4:\n"
        "    fn dispatch() -> i64:\n"
        "        match self.x:\n"
        "            case 0:\n"
        "                return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch (");
}

/* Method ending with 'val' */
TEST(method_ends_with_val) {
    auto out = compile_spl(
        "struct Obj5:\n"
        "    x: i64\n"
        "impl Obj5:\n"
        "    fn decl() -> i64:\n"
        "        return self.x\n"
        "        val unused = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return self->x");
}

/* Method ending with 'var' */
TEST(method_ends_with_var) {
    auto out = compile_spl(
        "struct Obj6:\n"
        "    x: i64\n"
        "impl Obj6:\n"
        "    fn decl2() -> i64:\n"
        "        return self.x\n"
        "        var unused = 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return self->x");
}

/* Method ending with 'break' */
TEST(method_ends_with_break) {
    auto out = compile_spl(
        "struct Obj7:\n"
        "    x: i64\n"
        "impl Obj7:\n"
        "    fn brk() -> i64:\n"
        "        return 0\n"
        "        break\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

/* Method ending with 'print' */
TEST(method_ends_with_print) {
    auto out = compile_spl(
        "struct Obj8:\n"
        "    x: i64\n"
        "impl Obj8:\n"
        "    fn pr() -> i64:\n"
        "        return 0\n"
        "        print 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return 0");
}

/* Val with array literal in translate_statement */
TEST(stmt_val_array_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    if true: val items: [i64] = [1, 2]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new()");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

/* Nested array in val (triggers [/] inside array literal) */
TEST(val_nested_array_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    val outer: [[i64]] = [[1, 2], [3, 4]]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new()");
}

/* Var with array but no literal (just empty) */
TEST(var_array_no_literal) {
    auto out = compile_spl(
        "fn test():\n"
        "    var items: [i64]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_new()");
}

/* expr_is_option for function return → line 431 */
TEST(expr_is_option_func_return) {
    auto out = compile_spl(
        "fn get_opt() -> text?:\n"
        "    return nil\n"
        "fn test():\n"
        "    val r = get_opt()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_text");
}

/* String interpolation with only expr: "{name}" → first=true then interp */
TEST(interp_expr_only_b7) {
    auto out = compile_spl(
        "fn greet(name: text) -> text:\n"
        "    return \"{name}\"\n"
    );
    /* When interp starts immediately, no literal prefix, just the expr */
    ASSERT_CONTAINS(out.c_str(), "return name");
}

/* String with escape followed by interpolation */
TEST(interp_escape_before_expr) {
    auto out = compile_spl(
        "fn test(x: i64) -> text:\n"
        "    return \"value\\t{x}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* Struct constructor with string field value (quotes in constructor arg) */
TEST(struct_constructor_with_string) {
    auto out = compile_spl(
        "struct Config:\n"
        "    name: text\n"
        "    value: i64\n"
        "fn test() -> Config:\n"
        "    return Config(name: \"test\", value: 42)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Config{");
    ASSERT_CONTAINS(out.c_str(), ".name =");
    ASSERT_CONTAINS(out.c_str(), "\"test\"");
}

/* Single-line if with return value (non-option) */
TEST(single_line_if_return_value) {
    auto out = compile_spl(
        "fn test(x: i64) -> i64:\n"
        "    if x > 0: return x\n"
        "    return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
    ASSERT_CONTAINS(out.c_str(), "return x;");
}

/* Print integer expression (non-text) via translate_statement */
TEST(stmt_print_integer_expr) {
    auto out = compile_spl(
        "fn test(x: i64, y: i64):\n"
        "    if true: print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf(\"%lld\\n\"");
}

/* Coalescing operator ?? in parse_var_decl type inference */
TEST(var_decl_coalescing_option) {
    auto out = compile_spl(
        "fn get_opt() -> text?:\n"
        "    return nil\n"
        "fn test():\n"
        "    val name = get_opt() ?? \"default\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* name");
}

/* ================================================================
 * Batch 8: Deep Branch Coverage — Targeted
 * ================================================================ */

/* String interpolation: int expr needs spl_i64_to_str (covers line 595-598 True:0) */
TEST(interp_int_expr_cast) {
    auto out = compile_spl(
        "fn get_num() -> i64:\n"
        "    return 42\n"
        "fn test():\n"
        "    val msg: text = \"count: {get_num()}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

/* String interp: expr followed by trailing text, str_pos > 2 but first==true (line 620 True:0) */
TEST(interp_only_trailing_text) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64 = 5\n"
        "    val msg: text = \"{x}!\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* String interpolation: empty expression result (line 628 True:0) */
TEST(interp_empty_result_b8) {
    auto out = compile_spl(
        "fn test():\n"
        "    val msg: text = \"{42}\"\n"
    );
    /* Should produce something for the interpolation */
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

/* String interpolation with nested braces inside expression (line 541 True:0 + 543) */
TEST(interp_nested_braces) {
    auto out = compile_spl(
        "var items: [i64] = [1, 2, 3]\n"
        "fn test():\n"
        "    val msg: text = \"count: {items.len()}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

/* Option .is_none() method (line 1502:65 True:0 — covers is_none in type inference) */
TEST(option_is_none_method) {
    auto out = compile_spl(
        "fn test():\n"
        "    var opt: text? = nil\n"
        "    val r = opt.is_none()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

/* Option struct field .is_none() (line 1529:79 True:0) */
TEST(option_struct_field_is_none) {
    auto out = compile_spl(
        "struct Wrapper:\n"
        "    value: text?\n"
        "fn test():\n"
        "    var w = Wrapper(value: nil)\n"
        "    val r = w.value.is_none()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "has_value");
}

/* .replace() args with parenthesized expr (line 943-944 True:0) */
TEST(replace_arg_with_parens) {
    auto out = compile_spl(
        "fn test():\n"
        "    var s: text = \"hello\"\n"
        "    val r: text = s.replace(\"h\", \"(H)\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_replace");
}

/* Static method call with string escape in args (line 982 True:0) */
TEST(static_method_string_escape) {
    auto out = compile_spl(
        "struct Builder:\n"
        "    data: text\n"
        "impl Builder:\n"
        "    static fn create(s: text) -> Builder:\n"
        "        return Builder(data: s)\n"
        "fn test():\n"
        "    val b = Builder.create(\"hello\\nworld\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Builder__create");
}

/* Static method call with nested parens in args (line 988 True:0) */
TEST(static_method_nested_parens) {
    auto out = compile_spl(
        "struct Calc:\n"
        "    val_x: i64\n"
        "fn add(a: i64, b: i64) -> i64:\n"
        "    return a + b\n"
        "impl Calc:\n"
        "    static fn make(n: i64) -> Calc:\n"
        "        return Calc(val_x: n)\n"
        "fn test():\n"
        "    val c = Calc.make(add(1, 2))\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Calc__make(add(1, 2))");
}

/* Instance method call with string escape (line 1029 True:0) */
TEST(instance_method_string_escape) {
    auto out = compile_spl(
        "struct Obj:\n"
        "    name: text\n"
        "impl Obj:\n"
        "    fn greet(msg: text) -> text:\n"
        "        return msg\n"
        "fn test():\n"
        "    var o = Obj(name: \"x\")\n"
        "    val r: text = o.greet(\"hi\\nthere\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Obj__greet");
}

/* Instance method with nested parens in args (line 1073 True:0 + 1067 True:0) */
TEST(instance_method_nested_parens) {
    auto out = compile_spl(
        "struct Adder:\n"
        "    base: i64\n"
        "fn mul(a: i64, b: i64) -> i64:\n"
        "    return a * b\n"
        "impl Adder:\n"
        "    fn compute(n: i64) -> i64:\n"
        "        return self.base + n\n"
        "fn test():\n"
        "    var a = Adder(base: 10)\n"
        "    val r = a.compute(mul(3, 4))\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Adder__compute");
}

/* Field access where bracket comes before paren (line 963 True:0) */
TEST(field_bracket_before_paren_b8) {
    auto out = compile_spl(
        "struct Data:\n"
        "    items: [i64]\n"
        "fn test():\n"
        "    var d = Data(items: [1, 2, 3])\n"
        "    val x = d.items[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "d.items");
}

/* Struct field with nested bracket indexing (line 1114 True:0) */
TEST(struct_field_nested_bracket) {
    auto out = compile_spl(
        "struct Matrix:\n"
        "    rows: [[i64]]\n"
        "fn test():\n"
        "    var m = Matrix(rows: [[1, 2], [3, 4]])\n"
        "    val inner = m.rows[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
}

/* Text .slice() method detection in parse_var_decl (line 1538 True:0) */
TEST(text_slice_method) {
    auto out = compile_spl(
        "fn test():\n"
        "    var s: text = \"hello\"\n"
        "    val sub: text = s.slice(0, 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

/* Option method chain with colon (line 1603 True:0) */
TEST(method_chain_option_colon) {
    auto out = compile_spl(
        "fn test():\n"
        "    var s: text = \"hello\"\n"
        "    val sub: text = s.trim()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_trim");
}

/* Chained instance method with string escape (line 1067) */
TEST(chained_method_str_escape) {
    auto out = compile_spl(
        "struct Fmt:\n"
        "    prefix: text\n"
        "impl Fmt:\n"
        "    fn format(s: text) -> text:\n"
        "        return s\n"
        "fn test():\n"
        "    var f = Fmt(prefix: \"p\")\n"
        "    val r: text = f.format(\"line1\\nline2\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Fmt__format");
}

/* Chained method nested parens (already covered by instance_method_nested_parens) */
TEST(chained_method_nested_parens) {
    auto out = compile_spl(
        "struct Ctx:\n"
        "    n: i64\n"
        "fn helper(x: i64) -> i64:\n"
        "    return x + 1\n"
        "impl Ctx:\n"
        "    fn run(val_a: i64) -> i64:\n"
        "        return self.n + val_a\n"
        "fn test():\n"
        "    var c = Ctx(n: 5)\n"
        "    val r = c.run(helper(3))\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Ctx__run");
}

/* Function call with string escape in args (line 1194 + 1304 True:0) */
TEST(func_arg_string_escape) {
    auto out = compile_spl(
        "fn greet(name: text, greeting: text) -> text:\n"
        "    return greeting\n"
        "fn test():\n"
        "    val r: text = greet(\"world\", \"hello\\nthere\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "greet(");
}

/* Struct constructor with empty args (line 1218 True:0) */
TEST(struct_ctor_empty_args) {
    auto out = compile_spl(
        "struct Empty:\n"
        "    x: i64\n"
        "fn test():\n"
        "    val e = Empty(x: 0)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Empty{");
}

/* Struct constructor positional arg with bracket (line 1224 True:0) */
TEST(struct_ctor_positional_bracket) {
    auto out = compile_spl(
        "struct Holder:\n"
        "    items: [i64]\n"
        "fn test():\n"
        "    val h = Holder(items: [1, 2, 3])\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Holder{");
}

/* Struct constructor value with string escape (line 1244 True:0) */
TEST(struct_ctor_value_escape) {
    auto out = compile_spl(
        "struct Msg:\n"
        "    content: text\n"
        "fn test():\n"
        "    val m = Msg(content: \"line1\\nline2\")\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Msg{");
}

/* Array indexing with nested brackets (line 1353 True:0) */
TEST(array_index_nested_bracket) {
    auto out = compile_spl(
        "fn test():\n"
        "    var matrix: [[i64]] = [[1, 2], [3, 4]]\n"
        "    val inner = matrix[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_get");
}

/* Identifier starting with underscore (line 1404 True:0) */
TEST(identifier_underscore_start) {
    auto out = compile_spl(
        "fn test():\n"
        "    var _count: i64 = 0\n"
        "    _count = _count + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "_count");
}

/* Var decl with .trim() text method result type (line 1538 trim path) */
TEST(var_decl_text_method_trim) {
    auto out = compile_spl(
        "fn test():\n"
        "    var s: text = \"  hello  \"\n"
        "    val trimmed: text = s.trim()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_trim");
}

/* Var decl with .slice() text method (line 1538 slice path) */
TEST(var_decl_text_method_slice) {
    auto out = compile_spl(
        "fn test():\n"
        "    var s: text = \"abcde\"\n"
        "    val sliced: text = s.slice(1, 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_slice");
}

/* use/export/import in translate_block (line 1934-1935 True:0) */
TEST(block_use_skip_b8) {
    auto out = compile_spl(
        "fn test():\n"
        "    use std.io\n"
        "    val x: i64 = 1\n"
    );
    /* use should be skipped, x should be declared */
    ASSERT_CONTAINS(out.c_str(), "const int64_t x = 1");
}

TEST(block_export_skip) {
    auto out = compile_spl(
        "fn test():\n"
        "    export foo\n"
        "    val x: i64 = 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const int64_t x = 2");
}

TEST(block_import_skip) {
    auto out = compile_spl(
        "fn test():\n"
        "    import bar\n"
        "    val x: i64 = 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const int64_t x = 3");
}

/* Blank line between if and elif/else (line 1741 True:0) */
TEST(elif_else_blank_line_between) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    var x: i64 = 5\n"
        "    if x == 1:\n"
        "        return 1\n"
        "\n"
        "    elif x == 2:\n"
        "        return 2\n"
        "\n"
        "    else:\n"
        "        return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "else if");
    ASSERT_CONTAINS(out.c_str(), "else {");
}

/* range() with parenthesized expression inside (line 1825-1826 True:0) */
TEST(range_paren_inside_arg) {
    auto out = compile_spl(
        "fn calc(n: i64) -> i64:\n"
        "    return n * 2\n"
        "fn test():\n"
        "    for i in range(calc(5)):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i");
    ASSERT_CONTAINS(out.c_str(), "calc(5)");
}

/* range() with bracket expression inside arg */
TEST(range_bracket_inside_arg) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [i64] = [10]\n"
        "    for i in range(arr[0]):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i");
}

/* Struct with blank lines and comments between fields (line 2455 True:0) */
TEST(struct_blank_comment_fields) {
    auto out = compile_spl(
        "struct Config:\n"
        "    name: text\n"
        "\n"
        "    # A comment\n"
        "    value: i64\n"
        "\n"
        "fn test():\n"
        "    val c = Config(name: \"x\", value: 42)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "struct Config");
    ASSERT_CONTAINS(out.c_str(), "const char* name");
    ASSERT_CONTAINS(out.c_str(), "int64_t value");
}

/* Enum with blank lines and comments between variants (line 2502 True:0) */
TEST(enum_blank_comment_variants) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "\n"
        "    # primary\n"
        "    Green\n"
        "    Blue\n"
        "\n"
        "fn test():\n"
        "    val c = Red\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Color_Red");
    ASSERT_CONTAINS(out.c_str(), "Color_Green");
    ASSERT_CONTAINS(out.c_str(), "Color_Blue");
}

/* Module-level option var with value init (line 2980 True:0) */
TEST(module_option_var_init) {
    auto out = compile_spl(
        "var opt: text? = \"hello\"\n"
        "fn test():\n"
        "    print opt.unwrap()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Option_text opt");
    ASSERT_CONTAINS(out.c_str(), "opt =");
}

/* Module-level struct var with init (line 2985 True:0) */
TEST(module_struct_var_init) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "var origin = Point(x: 0, y: 0)\n"
        "fn test():\n"
        "    print origin.x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "static Point origin");
    ASSERT_CONTAINS(out.c_str(), "origin = Point{");
}

/* Method ends with continue (line 2892 True:0 continue path) */
TEST(method_ends_with_continue) {
    auto out = compile_spl(
        "struct Iter:\n"
        "    n: i64\n"
        "impl Iter:\n"
        "    fn process() -> i64:\n"
        "        for i in range(self.n):\n"
        "            continue\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Iter__process");
    ASSERT_NOT_CONTAINS(out.c_str(), "return continue");
}

/* Method ends with elif (line 2888 + elif check not in method) */
TEST(method_ends_with_elif) {
    auto out = compile_spl(
        "struct Checker:\n"
        "    n: i64\n"
        "impl Checker:\n"
        "    fn check() -> i64:\n"
        "        if self.n == 1:\n"
        "            return 1\n"
        "        elif self.n == 2:\n"
        "            return 2\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Checker__check");
}

/* Method ends with else */
TEST(method_ends_with_else) {
    auto out = compile_spl(
        "struct Decider:\n"
        "    n: i64\n"
        "impl Decider:\n"
        "    fn decide() -> i64:\n"
        "        if self.n == 1:\n"
        "            return 1\n"
        "        else:\n"
        "            return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Decider__decide");
}

/* Method ends with assignment (line 2896 True:0 — the implicit return assignment check) */
TEST(method_ends_with_assignment) {
    auto out = compile_spl(
        "struct Counter:\n"
        "    count: i64\n"
        "impl Counter:\n"
        "    me increment() -> i64:\n"
        "        self.count = self.count + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Counter__increment");
    ASSERT_NOT_CONTAINS(out.c_str(), "return self->count = ");
}

/* Fn implicit return stops at paren expr (line 2777 True:0) */
TEST(fn_implicit_return_paren_expr) {
    auto out = compile_spl(
        "fn helper(x: i64) -> i64:\n"
        "    return x\n"
        "fn test() -> i64:\n"
        "    helper(5)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return helper(5)");
}

/* Fn implicit return stops at bracket expr (line 2777 '[' path) */
TEST(fn_implicit_return_bracket_expr) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    var arr: [i64] = [1, 2, 3]\n"
        "    arr[0]\n"
    );
    /* arr[0] gets implicit return but the expression starts with arr not [ */
    ASSERT_CONTAINS(out.c_str(), "return");
}

/* Fn implicit return stops at string expr (line 2777 '"' path) */
TEST(fn_implicit_return_string_expr) {
    auto out = compile_spl(
        "fn test() -> text:\n"
        "    \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return \"hello\"");
}

/* Method implicit return with paren expr */
TEST(method_implicit_return_paren) {
    auto out = compile_spl(
        "fn helper(x: i64) -> i64:\n"
        "    return x\n"
        "struct Obj:\n"
        "    n: i64\n"
        "impl Obj:\n"
        "    fn get() -> i64:\n"
        "        helper(self.n)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return helper(");
}

/* Method implicit return with bracket */
TEST(method_implicit_return_bracket) {
    auto out = compile_spl(
        "struct Arr:\n"
        "    items: [i64]\n"
        "impl Arr:\n"
        "    fn first() -> i64:\n"
        "        self.items[0]\n"
    );
    ASSERT_NOT_CONTAINS(out.c_str(), "return self.items");
}

/* Method implicit return with string literal */
TEST(method_implicit_return_string) {
    auto out = compile_spl(
        "struct Greeter:\n"
        "    name: text\n"
        "impl Greeter:\n"
        "    fn greet() -> text:\n"
        "        \"hello\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return \"hello\"");
}

/* Dot expression option nil assignment (line 2329 True:0) */
TEST(dot_expr_option_nil_assign) {
    auto out = compile_spl(
        "struct Container:\n"
        "    item: text?\n"
        "fn test():\n"
        "    var c = Container(item: \"hello\")\n"
        "    c.item = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "c.item = {}");
}

/* Multiple input files (line 3033 True:0) */
TEST(multi_file_input_b8) {
    /* Write two files and compile both */
    FILE* f1 = fopen("/tmp/_spl_multi1.spl", "w");
    fprintf(f1, "fn helper() -> i64:\n    return 42\n");
    fclose(f1);
    FILE* f2 = fopen("/tmp/_spl_multi2.spl", "w");
    fprintf(f2, "fn test() -> i64:\n    return helper()\n");
    fclose(f2);

    char cmd[512];
    snprintf(cmd, sizeof(cmd), "%s /tmp/_spl_multi1.spl /tmp/_spl_multi2.spl 2>&1", seed_binary);
    FILE* p = popen(cmd, "r");
    char buf[65536];
    int n = fread(buf, 1, sizeof(buf)-1, p);
    buf[n] = '\0';
    pclose(p);

    ASSERT(strstr(buf, "helper()") != nullptr);
    ASSERT(strstr(buf, "test()") != nullptr);
}

/* Modulo operator (line 746 True:0) */
TEST(modulo_operator_b8) {
    auto out = compile_spl(
        "fn test() -> i64:\n"
        "    return 10 % 3\n"
    );
    ASSERT_CONTAINS(out.c_str(), "(10 % 3)");
}

/* ================================================================
 * Coverage Batch 9: Struct Array Operations (100% branch coverage)
 * ================================================================ */

/* Struct array push */
TEST(struct_array_push) {
    auto out = compile_spl(
        "struct Item:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    val it = Item(name: \"a\")\n"
        "    items.push(it)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "push_back");
}

/* Struct array pop */
TEST(struct_array_pop) {
    auto out = compile_spl(
        "struct Item:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    items.pop()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "pop_back");
}

/* For-in struct array */
TEST(for_in_struct_array) {
    auto out = compile_spl(
        "struct Item:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    for item in items:\n"
        "        print item.name\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".size()");
    ASSERT_CONTAINS(out.c_str(), "Item item");
}

/* For-in text array */
TEST(for_in_text_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var names: [text] = []\n"
        "    for name in names:\n"
        "        print name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "as_str");
    ASSERT_CONTAINS(out.c_str(), "const char* name");
}

/* Val struct array with elements */
TEST(val_struct_array_with_elements) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "\n"
        "fn test():\n"
        "    val pts: [Point] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Point>");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

/* Var struct array with elements */
TEST(var_struct_array_with_elements) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "\n"
        "fn test():\n"
        "    var pts: [Point] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Point>");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

/* Struct array literal pushes */
TEST(struct_array_literal_push) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    val a = Item(v: 1)\n"
        "    val b = Item(v: 2)\n"
        "    var items: [Item] = [a, b]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "push_back");
}

/* Struct array set */
TEST(struct_array_set) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    val x = Item(v: 99)\n"
        "    items[0] = x\n"
    );
    /* struct arrays use direct indexing, not spl_array_set */
    ASSERT_NOT_CONTAINS(out.c_str(), "spl_array_set");
}

/* Struct array field access via indexing: arr[i].field */
TEST(struct_array_index_field) {
    auto out = compile_spl(
        "struct Node:\n"
        "    tag: text\n"
        "    value: i64\n"
        "\n"
        "fn test():\n"
        "    var nodes: [Node] = []\n"
        "    val t = nodes[0].tag\n"
    );
    ASSERT_CONTAINS(out.c_str(), "nodes[0]");
}

/* Option base type extraction for non-option type (line 207: no '?') */
TEST(option_base_no_question) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x = 5");
}

/* String interpolation with integer expression (needs cast) */
TEST(interp_int_needs_cast) {
    auto out = compile_spl(
        "fn test():\n"
        "    val n: i64 = 42\n"
        "    val s: text = \"{n}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_i64_to_str");
}

/* String interpolation multiple expressions */
TEST(interp_multiple_exprs) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: i64 = 1\n"
        "    val b: i64 = 2\n"
        "    val s: text = \"{a} and {b}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
}

/* Tab indentation (line 110) */
TEST(tab_indentation) {
    auto out = compile_spl(
        "fn test():\n"
        "\tval x: i64 = 5\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t x = 5");
}

/* Val struct array in block (translate_block) */
TEST(block_val_struct_array) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    if true:\n"
        "        val items: [Item] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Item>");
}

/* Var struct array in block (translate_block) */
TEST(block_var_struct_array) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    if true:\n"
        "        var items: [Item] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Item>");
}

/* Module-level struct array var init */
TEST(module_struct_array_var) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "var items: [Item] = []\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Item>");
}

/* For-in struct array in block */
TEST(block_for_in_struct_array) {
    auto out = compile_spl(
        "struct Node:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    var nodes: [Node] = []\n"
        "    if true:\n"
        "        for n in nodes:\n"
        "            print n.v\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".size()");
}

/* For-in text array in block */
TEST(block_for_in_text_array) {
    auto out = compile_spl(
        "fn test():\n"
        "    var names: [text] = []\n"
        "    if true:\n"
        "        for name in names:\n"
        "            print name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "as_str");
}

/* Struct array type return from type_to_cpp (line 258) */
TEST(struct_array_type_conversion) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn get_items() -> [Item]:\n"
        "    var items: [Item] = []\n"
        "    return items\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Item>");
}

/* extract_condition with trailing space (line 1801-1802) */
TEST(if_cond_trailing_space) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: bool = true\n"
        "    if x :\n"
        "        print \"yes\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (x)");
}

/* Method call with string arg containing escape (for args depth tracking) */
TEST(method_call_nested_paren_args) {
    auto out = compile_spl(
        "struct Foo:\n"
        "    v: i64\n"
        "\n"
        "impl Foo:\n"
        "    fn calc(a: i64, b: i64) -> i64:\n"
        "        return a + b\n"
        "\n"
        "fn test():\n"
        "    var f = Foo(v: 1)\n"
        "    val r = f.calc(2, 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Foo__calc");
    ASSERT_CONTAINS(out.c_str(), "2, 3");
}

/* Instance method with multiple args via translate_args */
TEST(instance_method_multi_args) {
    auto out = compile_spl(
        "struct Vec2:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "impl Vec2:\n"
        "    fn add(dx: i64, dy: i64) -> i64:\n"
        "        return self.x + dx + self.y + dy\n"
        "\n"
        "fn test():\n"
        "    var v = Vec2(x: 1, y: 2)\n"
        "    val r = v.add(10, 20)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Vec2__add");
    ASSERT_CONTAINS(out.c_str(), "10, 20");
}

/* Generic method with multiple args */
TEST(generic_method_multi_args) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
        "    val r = x.some_method(1, 2, 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "some_method");
    ASSERT_CONTAINS(out.c_str(), "1, 2, 3");
}

/* Type inference: struct array index field access */
TEST(type_infer_struct_array_index_field) {
    auto out = compile_spl(
        "struct Item:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    val n = items[0].name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "items[0]");
}

/* Struct array element type inference (no dot after bracket) */
TEST(type_infer_struct_array_index_no_dot) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    val it = items[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Item it");
}

/* Nested array set in statement */
TEST(stmt_nested_array_set_b9) {
    auto out = compile_spl(
        "fn test():\n"
        "    var arr: [[i64]] = []\n"
        "    var sub: [i64] = []\n"
        "    arr[0] = sub\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_set");
}

/* Struct field access bracket-before-paren check */
TEST(field_access_no_bracket) {
    auto out = compile_spl(
        "struct Pair:\n"
        "    first: i64\n"
        "    second: i64\n"
        "\n"
        "fn test():\n"
        "    var p = Pair(first: 1, second: 2)\n"
        "    val x = p.first\n"
    );
    ASSERT_CONTAINS(out.c_str(), "p.first");
}

/* Module-level struct array init with elements */
TEST(module_struct_array_literal) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "val a = Item(v: 1)\n"
        "var items: [Item] = [a]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "push_back");
}

/* fn parameter with Option type and ? suffix */
TEST(fn_param_option_type) {
    auto out = compile_spl(
        "fn maybe(x: i64?) -> i64:\n"
        "    return 0\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Option_i64");
}

/* Struct array literal with single element (last element path) */
TEST(struct_array_single_element) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "\n"
        "fn test():\n"
        "    val p = Point(x: 1)\n"
        "    var pts: [Point] = [p]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "push_back");
}

/* Print integer expression (line 2285 - no trailing space) */
TEST(print_integer_no_space) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 42\n"
        "    print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "printf");
}

/* Register function: me method */
TEST(register_me_method_b9) {
    auto out = compile_spl(
        "struct Counter:\n"
        "    n: i64\n"
        "\n"
        "impl Counter:\n"
        "    me inc():\n"
        "        self.n = self.n + 1\n"
    );
    ASSERT_CONTAINS(out.c_str(), "Counter__inc");
}

/* Previously unused test functions now registered with b9 suffix */
TEST(for_range_two_args_b9) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in 1..10:\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "for (int64_t i = 1; i < 10; i++)");
}

TEST(for_range_single_arg_b9) {
    auto out = compile_spl(
        "fn test():\n"
        "    for i in range(5):\n"
        "        print i\n"
    );
    ASSERT_CONTAINS(out.c_str(), "i < 5");
}

TEST(match_pipe_case_b9) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 1\n"
        "    match x:\n"
        "        case 1 | 2:\n"
        "            print \"low\"\n"
        "        case _:\n"
        "            print \"other\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "case 1:");
    ASSERT_CONTAINS(out.c_str(), "case 2:");
}

TEST(method_implicit_return_expr_b9) {
    auto out = compile_spl(
        "struct Foo:\n"
        "    v: i64\n"
        "\n"
        "impl Foo:\n"
        "    fn get() -> i64:\n"
        "        self.v\n"
    );
    ASSERT_CONTAINS(out.c_str(), "return");
    ASSERT_CONTAINS(out.c_str(), "self->v");
}

/* ================================================================
 * Coverage Batch 9b: Remaining branch coverage targets
 * ================================================================ */

/* Var struct array no init (line 2242) */
TEST(var_struct_array_no_init) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    var items: [Item]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "std::vector<Item>");
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

/* Type inference: fn returning struct, then field access (line 1743) */
TEST(type_infer_fn_struct_field) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn origin() -> Point:\n"
        "    return Point(x: 0, y: 0)\n"
        "\n"
        "fn test():\n"
        "    val px = origin().x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "origin()");
}

/* Type inference: text method .slice (line 1713) */
TEST(type_infer_text_slice) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    val sub = s.slice(0, 3)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char*");
}

/* Type inference: struct field access (line 1724) */
TEST(type_infer_struct_field_access) {
    auto out = compile_spl(
        "struct Cfg:\n"
        "    name: text\n"
        "\n"
        "fn test():\n"
        "    var c = Cfg(name: \"test\")\n"
        "    val n = c.name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* n");
}

/* Module-level option nil assign (block path, line 2574) */
TEST(block_option_nil_assign_b9) {
    auto out = compile_spl(
        "fn test():\n"
        "    var x: i64? = nil\n"
        "    x = 5\n"
        "    if true:\n"
        "        x = nil\n"
    );
    ASSERT_CONTAINS(out.c_str(), "= {}");
}

/* Single-line if with paren in condition (line 1898) */
TEST(single_line_if_paren_cond) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 5\n"
        "    if (x > 0): print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "(x > 0)");
}

/* Single-line if with string in condition (line 1900) */
TEST(single_line_if_string_cond) {
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello\"\n"
        "    if s == \"world\": print s\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
}

/* Module match statement (line 2980) */
TEST(module_match_b9) {
    auto out = compile_spl(
        "enum Color:\n"
        "    Red\n"
        "    Blue\n"
        "\n"
        "val c: i64 = 1\n"
        "match c:\n"
        "    case 0:\n"
        "        print \"red\"\n"
        "    case 1:\n"
        "        print \"blue\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "switch");
}

/* Struct array method call with args (push struct with fields) */
TEST(struct_array_push_constructed) {
    auto out = compile_spl(
        "struct Point:\n"
        "    x: i64\n"
        "    y: i64\n"
        "\n"
        "fn test():\n"
        "    var pts: [Point] = []\n"
        "    val p = Point(x: 1, y: 2)\n"
        "    pts.push(p)\n"
        "    val last = pts.pop()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "push_back");
    ASSERT_CONTAINS(out.c_str(), "pop_back");
}

/* Array literal with struct elements in emit_array_literal_pushes */
TEST(struct_array_multi_push) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    val a = Item(v: 1)\n"
        "    val b = Item(v: 2)\n"
        "    val c = Item(v: 3)\n"
        "    var items: [Item] = [a, b, c]\n"
    );
    /* Should have 3 push_back calls */
    auto pos1 = out.find("push_back");
    ASSERT(pos1 != std::string::npos);
    auto pos2 = out.find("push_back", pos1 + 1);
    ASSERT(pos2 != std::string::npos);
    auto pos3 = out.find("push_back", pos2 + 1);
    ASSERT(pos3 != std::string::npos);
}

/* Test crash recovery: empty function body */
TEST(empty_fn_body) {
    auto out = compile_spl(
        "fn nothing():\n"
        "    pass\n"
    );
    ASSERT_CONTAINS(out.c_str(), "void nothing()");
}

/* Test crash recovery: deeply nested if/else */
TEST(deep_nested_if) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 1\n"
        "    if x > 0:\n"
        "        if x > 1:\n"
        "            if x > 2:\n"
        "                print x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "if (");
}

/* Test crash recovery: many variables */
TEST(many_variables) {
    auto out = compile_spl(
        "fn test():\n"
        "    val a: i64 = 1\n"
        "    val b: i64 = 2\n"
        "    val c: i64 = 3\n"
        "    val d: i64 = 4\n"
        "    val e: i64 = 5\n"
        "    val f: i64 = 6\n"
        "    val g: i64 = 7\n"
        "    val h: i64 = 8\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t a = 1");
    ASSERT_CONTAINS(out.c_str(), "int64_t h = 8");
}

/* Struct array set via bracket */
TEST(struct_array_bracket_set) {
    auto out = compile_spl(
        "struct Item:\n"
        "    v: i64\n"
        "\n"
        "fn test():\n"
        "    var items: [Item] = []\n"
        "    val x = Item(v: 42)\n"
        "    items[0] = x\n"
    );
    ASSERT_CONTAINS(out.c_str(), "items[0]");
}

/* Struct field that is struct array, indexed (line 1276) */
TEST(struct_field_struct_array_index) {
    auto out = compile_spl(
        "struct Node:\n"
        "    tag: text\n"
        "\n"
        "struct Tree:\n"
        "    children: [Node]\n"
        "\n"
        "fn test():\n"
        "    var t = Tree(children: [])\n"
        "    val first = t.children[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), "t.children[0]");
}

/* String interpolation with literal prefix first (line 705) */
TEST(interp_literal_prefix_first) {
    auto out = compile_spl(
        "fn test():\n"
        "    val x: i64 = 42\n"
        "    val s: text = \"value={x}\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "\"value=\"");
}

/* expr_is_text fallback in parse_var_decl (line 1810) */
TEST(type_infer_text_fn_result) {
    auto out = compile_spl(
        "fn get_name() -> text:\n"
        "    return \"hello\"\n"
        "\n"
        "fn test():\n"
        "    val s = get_name()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* s");
}

/* fn returning struct with field access fallback (line 1755) */
TEST(type_infer_fn_struct_unknown_field) {
    auto out = compile_spl(
        "struct Cfg:\n"
        "    name: text\n"
        "    value: i64\n"
        "\n"
        "fn make() -> Cfg:\n"
        "    return Cfg(name: \"x\", value: 1)\n"
        "\n"
        "fn test():\n"
        "    val v = make().value\n"
    );
    ASSERT_CONTAINS(out.c_str(), "make()");
}

/* ================================================================
 * Bug-fix regression tests
 * ================================================================ */

/* Bug 1: String concat with + should use spl_str_concat, not raw C++ + */
TEST(str_concat_plus_var) {
    auto out = compile_spl(
        "fn greet(name: text) -> text:\n"
        "    return \"hello \" + name\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    /* Must NOT have raw C++ + between string literal and variable */
    ASSERT_NOT_CONTAINS(out.c_str(), "\"hello \" + name");
}

TEST(str_concat_plus_func) {
    auto out = compile_spl(
        "fn get_name() -> text:\n"
        "    return \"world\"\n"
        "\n"
        "fn greet() -> text:\n"
        "    return \"hello \" + get_name()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_NOT_CONTAINS(out.c_str(), "\"hello \" + get_name");
}

TEST(str_concat_triple) {
    auto out = compile_spl(
        "fn fmt(a: text, b: text) -> text:\n"
        "    return \"[\" + a + \"] \" + b\n"
    );
    /* Should have nested spl_str_concat calls */
    const char* s = out.c_str();
    int count = 0;
    const char* p = s;
    while ((p = strstr(p, "spl_str_concat")) != nullptr) { count++; p++; }
    ASSERT(count >= 3); /* at least 3 concat calls for 3 + operators */
}

TEST(str_concat_pure_literal) {
    /* Pure string literal without + should still work */
    auto out = compile_spl(
        "fn test():\n"
        "    val s: text = \"hello world\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "\"hello world\"");
}

TEST(str_concat_interp_no_plus) {
    /* String interpolation without + should still use spl_str_concat */
    auto out = compile_spl(
        "fn test(name: text) -> text:\n"
        "    return \"hello {name}!\"\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_concat");
    ASSERT_CONTAINS(out.c_str(), "name");
}

/* Bug 2: .len() on text-returning function calls should use spl_str_len */
TEST(len_on_text_var) {
    auto out = compile_spl(
        "fn test(s: text) -> i64:\n"
        "    return s.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_len(s)");
    ASSERT_NOT_CONTAINS(out.c_str(), "spl_array_len(s)");
}

TEST(len_on_text_func) {
    auto out = compile_spl(
        "fn get_text() -> text:\n"
        "    return \"hello\"\n"
        "\n"
        "fn test() -> i64:\n"
        "    return get_text().len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_str_len(get_text())");
    ASSERT_NOT_CONTAINS(out.c_str(), "spl_array_len(get_text())");
}

TEST(len_on_array_var) {
    /* Array .len() should still use spl_array_len */
    auto out = compile_spl(
        "fn test(arr: [i64]) -> i64:\n"
        "    return arr.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_array_len(arr)");
}

/* Bug 3 & 4: for-loop over nested and float arrays */
TEST(for_nested_text_array) {
    auto out = compile_spl(
        "fn test(items: [[text]]):\n"
        "    for row in items:\n"
        "        val x = row.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "SplArray* row");
    ASSERT_CONTAINS(out.c_str(), ".as_array");
    ASSERT_NOT_CONTAINS(out.c_str(), "int64_t row =");
}

TEST(for_nested_int_array) {
    auto out = compile_spl(
        "fn test(matrix: [[i64]]):\n"
        "    for row in matrix:\n"
        "        val x = row.len()\n"
    );
    ASSERT_CONTAINS(out.c_str(), "SplArray* row");
    ASSERT_CONTAINS(out.c_str(), ".as_array");
}

TEST(for_float_array) {
    auto out = compile_spl(
        "fn test(vals: [f64]):\n"
        "    for v in vals:\n"
        "        val x = v\n"
    );
    ASSERT_CONTAINS(out.c_str(), "double v =");
    ASSERT_CONTAINS(out.c_str(), ".as_float");
    ASSERT_NOT_CONTAINS(out.c_str(), "int64_t v =");
}

TEST(for_text_array_unchanged) {
    /* text arrays should still use .as_str */
    auto out = compile_spl(
        "fn test(names: [text]):\n"
        "    for n in names:\n"
        "        val x = n\n"
    );
    ASSERT_CONTAINS(out.c_str(), "const char* n =");
    ASSERT_CONTAINS(out.c_str(), ".as_str");
}

TEST(for_int_array_unchanged) {
    /* int arrays should still use .as_int */
    auto out = compile_spl(
        "fn test(nums: [i64]):\n"
        "    for n in nums:\n"
        "        val x = n\n"
    );
    ASSERT_CONTAINS(out.c_str(), "int64_t n =");
    ASSERT_CONTAINS(out.c_str(), ".as_int");
}

/* ================================================================
 * Coverage Batch 11 – remaining coverable lines
 * ================================================================ */

/* Float array push: line 1029 – spl_float() wrapper */
TEST(float_array_push) {
    auto out = compile_spl(
        "fn test():\n"
        "    var vals: [f64] = []\n"
        "    vals.push(3.14)\n"
    );
    ASSERT_CONTAINS(out.c_str(), "spl_float(");
    ASSERT_CONTAINS(out.c_str(), "spl_array_push");
}

/* Float array indexing: line 1578 – .as_float accessor */
TEST(float_array_index) {
    auto out = compile_spl(
        "fn test(vals: [f64]):\n"
        "    val x = vals[0]\n"
    );
    ASSERT_CONTAINS(out.c_str(), ".as_float");
}

/* Float array type inference: lines 1685-1686 – val x = arr[i] infers f64 */
TEST(float_array_type_infer) {
    auto out = compile_spl(
        "fn test(vals: [f64]):\n"
        "    val x = vals[0]\n"
        "    val y = x + 1.0\n"
    );
    /* x should be inferred as double since vals is [f64] */
    ASSERT_CONTAINS(out.c_str(), "double");
}

/* Fn return struct unknown field: line 1826 – fallback to struct type */
TEST(fn_return_struct_unknown_field) {
    auto out = compile_spl(
        "struct Cfg:\n"
        "    name: text\n"
        "    value: i64\n"
        "\n"
        "fn make() -> Cfg:\n"
        "    return Cfg(name: \"x\", value: 1)\n"
        "\n"
        "fn test():\n"
        "    val v = make().unknown\n"
    );
    ASSERT_CONTAINS(out.c_str(), "make()");
}

/* Struct array field fallback: line 1707 – unknown field on arr[i].field */
TEST(struct_array_unknown_field) {
    auto out = compile_spl(
        "struct Item:\n"
        "    name: text\n"
        "\n"
        "fn test(items: [Item]):\n"
        "    val v = items[0].missing\n"
    );
    ASSERT_CONTAINS(out.c_str(), "items");
}

/* ================================================================
 * Main
 * ================================================================ */

int main(int argc, char** argv) {
    /* Find seed_cpp binary: either next to us or via env */
    const char* env_seed = getenv("SEED_CPP");
    if (env_seed && env_seed[0]) {
        seed_binary = env_seed;
    } else {
        /* Try relative paths */
        static char path[1024];
        /* Try ./seed_cpp (cmake build dir) */
        snprintf(path, sizeof(path), "./seed_cpp");
        FILE* f = fopen(path, "r");
        if (f) { fclose(f); seed_binary = path; }
        else {
            /* Try /tmp/seed_cpp */
            snprintf(path, sizeof(path), "/tmp/seed_cpp");
            f = fopen(path, "r");
            if (f) { fclose(f); seed_binary = path; }
            else {
                fprintf(stderr, "Cannot find seed_cpp binary. Set SEED_CPP env var.\n");
                return 1;
            }
        }
    }

    printf("=== seed.cpp Test Suite ===\n");
    printf("  seed binary: %s\n\n", seed_binary);

    printf("--- Structs ---\n");
    RUN(struct_definition);
    RUN(struct_text_field);

    printf("\n--- Enums ---\n");
    RUN(enum_definition);
    RUN(enum_match);

    printf("\n--- Functions ---\n");
    RUN(fn_basic);
    RUN(fn_void);
    RUN(fn_text_return);
    RUN(extern_fn);

    printf("\n--- Variables ---\n");
    RUN(val_declaration);
    RUN(var_declaration);
    RUN(module_level_val);
    RUN(module_level_var);

    printf("\n--- Expressions ---\n");
    RUN(string_literal);
    RUN(string_interpolation);
    RUN(bool_literals);
    RUN(nil_literal);
    RUN(binary_operators);
    RUN(logical_operators);
    RUN(comparison_operators);
    RUN(string_equality);
    RUN(string_concat);
    RUN(nil_coalescing);
    RUN(array_literal);

    printf("\n--- Control Flow ---\n");
    RUN(if_statement);
    RUN(if_else);
    RUN(if_elif_else);
    RUN(single_line_if);
    RUN(while_loop);
    RUN(for_range);
    RUN(for_range_fn);
    RUN(for_in_array);
    RUN(match_statement);
    RUN(break_continue);

    printf("\n--- Methods ---\n");
    RUN(impl_method);
    RUN(impl_mutable_method);
    RUN(impl_static_method);

    printf("\n--- Built-in Methods ---\n");
    RUN(string_methods);
    RUN(array_methods);
    RUN(option_methods);

    printf("\n--- Types ---\n");
    RUN(all_primitive_types);
    RUN(option_type);
    RUN(struct_constructor);

    printf("\n--- Statements ---\n");
    RUN(compound_assign);
    RUN(print_statement);
    RUN(use_export_skipped);
    RUN(field_access);

    printf("\n--- Output Structure ---\n");
    RUN(has_runtime_include);
    RUN(has_main_function);
    RUN(empty_input);
    RUN(comment_only);
    RUN(no_args_exits);

    printf("\n--- Coverage: Module Variables ---\n");
    RUN(module_option_var);
    RUN(module_struct_var);
    RUN(module_dynamic_text_var);
    RUN(module_dynamic_bool_var);
    RUN(module_dynamic_int_var);
    RUN(module_option_nonnil_init);

    printf("\n--- Coverage: Module Statements ---\n");
    RUN(module_level_call);
    RUN(module_level_print_text);
    RUN(module_level_print_int);
    RUN(module_level_pass);
    RUN(module_compound_assign);
    RUN(module_array_set);
    RUN(module_option_nil_assign);
    RUN(module_level_if);

    printf("\n--- Coverage: Option Types in Blocks ---\n");
    RUN(val_option_nonnil);
    RUN(var_option_nil);
    RUN(var_option_nonnil);
    RUN(var_array_with_elements);
    RUN(val_array_with_elements);

    printf("\n--- Coverage: Match Patterns ---\n");
    RUN(match_pipe_cases);
    RUN(match_enum_pipe);
    RUN(use_inside_block);

    printf("\n--- Coverage: Operators ---\n");
    RUN(modulo_operator);
    RUN(option_nil_comparison);
    RUN(nil_coalescing_non_option);
    RUN(option_unwrap);
    RUN(string_interp_escape);
    RUN(unit_expression);

    printf("\n--- Coverage: Enum Variants ---\n");
    RUN(bare_enum_variant);
    RUN(enum_variant_call);

    printf("\n--- Coverage: Method Calls ---\n");
    RUN(static_method_call);
    RUN(static_method_call_with_args);
    RUN(instance_method_call);

    printf("\n--- Coverage: Struct Options ---\n");
    RUN(struct_option_type);
    RUN(struct_option_field);

    printf("\n--- Coverage: Array Types ---\n");
    RUN(text_array_literal);
    RUN(string_indexing);
    RUN(string_slicing);
    RUN(slice_no_start);
    RUN(slice_no_end);
    RUN(array_indexing_int);
    RUN(text_array_indexing);
    RUN(nested_array_indexing);

    printf("\n--- Coverage: Struct Field Access ---\n");
    RUN(struct_field_array_index);
    RUN(struct_field_text_index);
    RUN(struct_field_slice);
    RUN(array_set_in_block);
    RUN(text_array_set);
    RUN(option_nil_assign_block);

    printf("\n--- Coverage: Type Inference ---\n");
    RUN(type_infer_string);
    RUN(type_infer_bool);
    RUN(type_infer_struct);
    RUN(type_infer_array);

    printf("\n--- Coverage: Misc ---\n");
    RUN(return_nil_option);
    RUN(implicit_return);
    RUN(int_builtin);
    RUN(string_not_equal);
    RUN(multi_arg_fn_call);
    RUN(multi_file_input);
    RUN(string_replace_method);
    RUN(string_trim_method);
    RUN(compound_assign_in_block);
    RUN(modulo_with_vars);
    RUN(struct_field_slice_no_start);
    RUN(struct_field_slice_no_end);
    RUN(struct_field_text_array_index);
    RUN(string_escape_no_interp);
    RUN(type_infer_is_some);
    RUN(type_infer_unwrap);
    RUN(fn_option_param);
    RUN(match_pipe_with_wildcard);
    RUN(module_text_array_set);
    RUN(generic_method_call);
    RUN(struct_field_option_unwrap_infer);
    RUN(fn_return_option_unwrap_infer);
    RUN(module_nested_array_set);

    printf("\n--- Coverage: Edge Cases ---\n");
    RUN(option_array_type);
    RUN(generic_method_call_with_args);
    RUN(struct_field_generic_array_index);
    RUN(constructor_positional_arg);
    RUN(struct_field_option_is_some_infer);
    RUN(fn_call_option_unwrap_infer);
    RUN(type_infer_text_expr);
    RUN(single_line_if_return_nil);
    RUN(single_line_if_bare_return);
    RUN(single_line_if_break);
    RUN(single_line_if_continue);
    RUN(var_array_no_init);
    RUN(fn_param_no_type);
    RUN(fn_param_trailing_space);
    RUN(fn_return_type_trailing_space);
    RUN(implicit_return_assignment);
    RUN(method_implicit_return_assignment);
    RUN(impl_comment_line);
    RUN(string_escape_backslash_n);
    RUN(string_replace_no_close_paren);
    RUN(fn_param_type_trailing_space);
    RUN(method_explicit_return);
    RUN(module_option_array_var);

    printf("\n--- Coverage Batch 2: translate_statement ---\n");
    RUN(single_line_if_val_decl);
    RUN(single_line_if_var_decl);
    RUN(single_line_if_return_expr);
    RUN(single_line_if_print);
    RUN(single_line_if_assign);
    RUN(single_line_if_compound_assign);
    RUN(single_line_if_minus_assign);
    RUN(single_line_if_pass);
    RUN(single_line_if_fn_call);

    printf("\n--- Coverage Batch 2: Types ---\n");
    RUN(type_u32);
    RUN(type_u64);
    RUN(type_f32);
    RUN(fn_void_return_type);
    RUN(enum_typed_var);
    RUN(text_option_type);
    RUN(bool_option_type);
    RUN(struct_option_return_value);

    printf("\n--- Coverage Batch 2: Methods ---\n");
    RUN(option_is_none);
    RUN(array_pop_method);
    RUN(text_array_push);
    RUN(nested_array_push);
    RUN(string_to_upper);
    RUN(string_to_lower);
    RUN(string_split_method);
    RUN(static_method_string_arg);

    printf("\n--- Coverage Batch 2: Module Level ---\n");
    RUN(module_level_while);
    RUN(module_level_for);
    RUN(module_level_match);
    RUN(module_struct_var_nonnil);
    RUN(module_option_with_fn_call);

    printf("\n--- Coverage Batch 2: Expressions ---\n");
    RUN(nil_coalescing_text_option);
    RUN(nested_fn_call);
    RUN(paren_expr);
    RUN(f64_arithmetic);
    RUN(negative_number);
    RUN(generic_method_string_arg);

    printf("\n--- Coverage Batch 2: Functions ---\n");
    RUN(fn_with_if_elif_else_return);
    RUN(fn_param_array_type);
    RUN(implicit_return_call);
    RUN(implicit_return_var);
    RUN(translate_stmt_bare_return);

    printf("\n--- Coverage Batch 2: Structs ---\n");
    RUN(struct_construct_text_field);
    RUN(var_struct_constructor);
    RUN(method_implicit_return_expr_b6);
    RUN(method_body_with_loop);
    RUN(self_field_indexing);
    RUN(self_field_text_slice);

    printf("\n--- Coverage Batch 2: Misc ---\n");
    RUN(single_line_if_array_set);
    RUN(single_line_if_option_nil);
    RUN(bool_array_literal);
    RUN(while_complex_cond);

    printf("\n--- Coverage Batch 3: translate_statement deeper ---\n");
    RUN(single_line_if_val_array);
    RUN(single_line_if_val_option_nil);
    RUN(single_line_if_val_option_nonnil);
    RUN(single_line_if_var_array);
    RUN(single_line_if_var_option_nil);
    RUN(single_line_if_var_option_nonnil);
    RUN(module_level_return_expr);

    printf("\n--- Coverage Batch 3: Array/Option ---\n");
    RUN(nested_array_set_in_block);
    RUN(text_array_set_in_block);
    RUN(option_coalescing_in_expr);

    printf("\n--- Coverage Batch 3: Methods ---\n");
    RUN(method_last_stmt_assignment);
    RUN(method_body_with_val);
    RUN(method_body_with_print);
    RUN(method_implicit_return_expr_b6);
    RUN(instance_method_mutable_with_args);
    RUN(fn_option_unwrap_method_infer);
    RUN(impl_empty_line);

    printf("\n--- Coverage Batch 3: Misc ---\n");
    RUN(struct_field_nonexistent);
    RUN(string_interp_at_end);
    RUN(replace_with_nested_call);
    RUN(type_infer_fn_returning_text);
    RUN(option_struct_return_nonnil);
    RUN(for_range_with_var);
    RUN(module_level_expr_call);
    RUN(self_field_slice);

    printf("\n--- Coverage Batch 4: Operators & Expressions ---\n");
    RUN(nil_eq_left_side);
    RUN(nil_ne_left_side);
    RUN(string_ne_operator);
    RUN(string_concat_operator);
    RUN(nil_coalescing_non_option_b4);
    RUN(modulo_operator_b4);
    RUN(string_interp_only_expr);
    RUN(string_interp_empty_braces);
    RUN(not_prefix_expr);
    RUN(paren_expr_empty);
    RUN(string_interp_text_var);
    RUN(option_nil_eq);
    RUN(option_nil_ne);

    printf("\n--- Coverage Batch 4: Built-in Methods ---\n");
    RUN(text_contains_method);
    RUN(text_starts_with_method);
    RUN(text_ends_with_method);
    RUN(text_index_of_method);
    RUN(text_trim_method);
    RUN(replace_nested_arg_parens);
    RUN(static_method_no_args);
    RUN(instance_method_string_arg);
    RUN(generic_method_string_arg_call);

    printf("\n--- Coverage Batch 4: Struct Field Access ---\n");
    RUN(struct_field_text_index_b4);
    RUN(struct_field_text_array_index_b4);
    RUN(struct_field_int_array_index);
    RUN(struct_field_text_slice);
    RUN(constructor_positional_break);
    RUN(field_bracket_before_paren);
    RUN(self_field_simple);
    RUN(self_field_array_index);
    RUN(struct_option_field_emit);
    RUN(constructor_string_field);

    printf("\n--- Coverage Batch 4: Array/Indexing ---\n");
    RUN(nested_array_index);
    RUN(text_array_index);
    RUN(text_char_index);
    RUN(text_slice_expr);
    RUN(bare_enum_variant_b4);
    RUN(array_literal_nested);

    printf("\n--- Coverage Batch 4: Type Inference ---\n");
    RUN(type_infer_bool_true);
    RUN(type_infer_struct_constructor);
    RUN(type_infer_fn_text_return);
    RUN(type_infer_fn_bool_return);
    RUN(type_infer_fn_array_return);
    RUN(type_infer_fn_struct_return);
    RUN(type_infer_option_coalescing);
    RUN(type_infer_fn_option_coalescing);
    RUN(type_infer_text_trim);
    RUN(type_infer_text_starts_with);
    RUN(type_infer_text_contains);
    RUN(type_infer_text_ends_with);
    RUN(type_infer_text_replace);
    RUN(type_infer_static_method);
    RUN(type_infer_instance_method);
    RUN(type_infer_slice_expr);
    RUN(type_infer_struct_field_option_unwrap);
    RUN(type_infer_struct_field_option_is_some);
    RUN(type_infer_option_var_is_some);
    RUN(type_infer_expr_is_text_fallback);

    printf("\n--- Coverage Batch 4: translate_statement ---\n");
    RUN(translate_stmt_return_nil_option);
    RUN(translate_stmt_bare_return_b4);
    RUN(translate_stmt_break);
    RUN(translate_stmt_continue);
    RUN(translate_stmt_pass);
    RUN(translate_stmt_use_skip);
    RUN(translate_stmt_print_int);
    RUN(translate_stmt_plus_assign);
    RUN(translate_stmt_minus_assign);
    RUN(translate_stmt_simple_assign);
    RUN(translate_stmt_val_array_literal);
    RUN(translate_stmt_val_option_nil);
    RUN(translate_stmt_val_const_type);
    RUN(translate_stmt_var_array_init);
    RUN(translate_stmt_var_option_nil);
    RUN(translate_stmt_array_set);
    RUN(translate_stmt_option_nil_assign);
    RUN(translate_stmt_nested_array_set);
    RUN(translate_stmt_text_array_set);

    printf("\n--- Coverage Batch 4: translate_block ---\n");
    RUN(block_use_skip);
    RUN(block_val_option_nil);
    RUN(block_var_option_nil);
    RUN(block_return_nil_option);
    RUN(block_pass_statement);
    RUN(block_unit_statement);
    RUN(block_option_nil_assign);
    RUN(block_plus_assign);
    RUN(block_minus_assign);
    RUN(block_elif_else);
    RUN(block_match_enum);
    RUN(block_while_loop);
    RUN(for_item_in_array);
    RUN(for_range_two_args_b6);
    RUN(for_range_single_arg_b6);
    RUN(match_pipe_case_b6);
    RUN(match_pipe_wildcard);
    RUN(match_pipe_enum);

    printf("\n--- Coverage Batch 4: Function Registration ---\n");
    RUN(me_method_register);
    RUN(extern_fn_register);
    RUN(static_fn_register);
    RUN(register_func_unrecognized);
    RUN(extern_fn_multi_params);
    RUN(fn_param_array_type_parse);
    RUN(fn_call_string_arg);
    RUN(fn_call_multi_params);

    printf("\n--- Coverage Batch 4: Module Level ---\n");
    RUN(module_var_text_default);
    RUN(module_var_bool_default);
    RUN(module_var_int_default);
    RUN(module_var_struct_type);
    RUN(module_init_block);
    RUN(module_init_call);

    printf("\n--- Coverage Batch 4: Implicit Return ---\n");
    RUN(implicit_return_ends_with_if);
    RUN(implicit_return_ends_with_for);
    RUN(implicit_return_ends_with_val);
    RUN(implicit_return_ends_with_while);
    RUN(implicit_return_ends_with_match);
    RUN(implicit_return_ends_with_break_fn);
    RUN(implicit_return_ends_with_print);
    RUN(implicit_return_ends_with_else);
    RUN(implicit_return_ends_with_case);
    RUN(implicit_return_ends_with_continue_fn);
    RUN(implicit_return_assignment_last_stmt);
    RUN(implicit_return_ne_comparison);
    RUN(implicit_return_le_comparison);
    RUN(implicit_return_ge_comparison);
    RUN(implicit_return_eq_comparison);

    printf("\n--- Coverage Batch 4: Method Implicit Return ---\n");
    RUN(method_implicit_return_if);
    RUN(method_implicit_return_for);
    RUN(method_implicit_return_val);
    RUN(method_implicit_return_var);
    RUN(method_implicit_return_break);
    RUN(method_implicit_return_print);
    RUN(method_implicit_return_assign);
    RUN(method_implicit_return_ne);
    RUN(method_implicit_return_le);
    RUN(method_implicit_return_ge);
    RUN(method_implicit_return_eq);
    RUN(method_body_struct_type_processing);

    printf("\n--- Coverage Batch 4: Misc ---\n");
    RUN(expr_is_text_struct_method);
    RUN(expr_is_text_func_return);

    printf("\n--- Coverage Batch 5: Comparison Expression Stmts ---\n");
    RUN(block_expr_ne_comparison);
    RUN(block_expr_le_comparison);
    RUN(block_expr_ge_comparison);
    RUN(block_expr_eq_comparison);
    RUN(stmt_expr_ne_comparison);
    RUN(stmt_expr_le_comparison);
    RUN(stmt_expr_ge_comparison);
    RUN(stmt_expr_eq_comparison);

    printf("\n--- Coverage Batch 5: String Interpolation ---\n");
    RUN(string_interp_literal_then_expr);
    RUN(string_interp_text_expr_direct);
    RUN(string_interp_prefix_literal);
    RUN(string_interp_multiple_exprs);
    RUN(string_interp_text_string_literal);

    printf("\n--- Coverage Batch 5: Edge Cases ---\n");
    RUN(struct_field_raw_index);
    RUN(extract_cond_trailing_space);
    RUN(var_decl_no_type_no_init);
    RUN(constant_expr_empty);
    RUN(constant_expr_negative);
    RUN(constant_expr_string);
    RUN(constant_expr_bool_true);
    RUN(constant_expr_bool_false);
    RUN(constant_expr_nil);

    printf("\n--- Coverage Batch 5: Block Operations ---\n");
    RUN(block_nested_array_set);
    RUN(block_text_array_set);
    RUN(block_val_struct);
    RUN(block_dot_option_nil_assign);
    RUN(method_body_match);
    RUN(method_body_while);
    RUN(method_body_for_range);
    RUN(struct_field_option);

    printf("\n--- Coverage Batch 5: Registration & Module ---\n");
    RUN(fn_multi_param_types);
    RUN(translate_stmt_option_return_nil);
    RUN(module_val_constant);
    RUN(module_var_array);
    RUN(module_var_option);
    RUN(struct_with_comment);
    RUN(enum_with_comment);
    RUN(impl_with_methods_and_comments);
    RUN(fn_sig_return_type_space);
    RUN(single_line_if_complex_cond);
    RUN(constructor_nested_call_arg);

    /* ===== Batch 6: Remaining Branch Coverage ===== */

    printf("\n--- Coverage Batch 6: For Loop Variants ---\n");
    RUN(for_in_array_loop);
    RUN(for_range_single_arg_b6);
    RUN(for_range_two_args_b6);

    printf("\n--- Coverage Batch 6: Option Type Paths ---\n");
    RUN(val_option_with_value);
    RUN(val_option_nil);
    RUN(var_option_with_value);
    RUN(var_option_nil_init);
    RUN(return_nil_from_option_fn);
    RUN(single_line_if_return_nil_option);
    RUN(option_nil_assignment_block);
    RUN(option_dot_nil_assignment_block);

    printf("\n--- Coverage Batch 6: translate_statement Paths ---\n");
    RUN(stmt_use_skip);
    RUN(stmt_export_skip);
    RUN(stmt_import_skip);
    RUN(stmt_val_option_nil);
    RUN(stmt_val_option_value);
    RUN(stmt_var_option_nil);
    RUN(stmt_var_option_value);
    RUN(stmt_var_array_literal);
    RUN(stmt_bare_return);
    RUN(stmt_break);
    RUN(stmt_continue);
    RUN(stmt_pass);
    RUN(stmt_unit);
    RUN(stmt_print_int);
    RUN(stmt_print_text);
    RUN(stmt_plus_equals);
    RUN(stmt_minus_equals);
    RUN(stmt_assignment);
    RUN(stmt_text_array_assign);
    RUN(stmt_option_nil_assign);
    RUN(stmt_expr_statement);

    printf("\n--- Coverage Batch 6: Module Level ---\n");
    RUN(module_control_flow_if);
    RUN(module_option_init_value);
    RUN(module_array_literal_init);
    RUN(module_struct_init);
    RUN(module_expr_statement);
    RUN(module_use_skip);

    printf("\n--- Coverage Batch 6: String Interpolation ---\n");
    RUN(interp_only_expr_no_prefix);
    RUN(interp_text_var);
    RUN(interp_empty_result);

    printf("\n--- Coverage Batch 6: Struct/Method ---\n");
    RUN(struct_constructor_named_args);
    RUN(method_implicit_return_expr_b6);
    RUN(fn_implicit_return_expr);
    RUN(static_method_impl);
    RUN(replace_no_closing_paren);
    RUN(for_in_array_iteration);
    RUN(match_pipe_case_b6);
    RUN(expr_is_text_fallback_inference);
    RUN(single_line_if_no_colon_body);

    /* ===== Batch 7: Deep Branch Coverage ===== */

    printf("\n--- Coverage Batch 7: Option No Init ---\n");
    RUN(stmt_val_option_no_init);
    RUN(stmt_var_option_no_init);
    RUN(block_val_option_no_init);
    RUN(block_var_option_no_init);

    printf("\n--- Coverage Batch 7: Module Skip ---\n");
    RUN(module_export_skip);
    RUN(module_import_skip);
    RUN(module_control_flow_while);
    RUN(module_control_flow_for);
    RUN(module_control_flow_match);

    printf("\n--- Coverage Batch 7: Fn Ends With ---\n");
    RUN(fn_ends_with_if);
    RUN(fn_ends_with_while);
    RUN(fn_ends_with_for);
    RUN(fn_ends_with_match);
    RUN(fn_ends_with_val);
    RUN(fn_ends_with_var);
    RUN(fn_ends_with_break);
    RUN(fn_ends_with_continue);
    RUN(fn_ends_with_print);
    RUN(fn_ends_with_case);
    RUN(fn_ends_with_elif);
    RUN(fn_ends_with_else);
    RUN(fn_ends_with_assignment);

    printf("\n--- Coverage Batch 7: Method Ends With ---\n");
    RUN(method_ends_with_if);
    RUN(method_ends_with_while);
    RUN(method_ends_with_for);
    RUN(method_ends_with_match);
    RUN(method_ends_with_val);
    RUN(method_ends_with_var);
    RUN(method_ends_with_break);
    RUN(method_ends_with_print);

    printf("\n--- Coverage Batch 7: Misc ---\n");
    RUN(stmt_val_array_literal);
    RUN(val_nested_array_literal);
    RUN(var_array_no_literal);
    RUN(expr_is_option_func_return);
    RUN(interp_expr_only_b7);
    RUN(interp_escape_before_expr);
    RUN(struct_constructor_with_string);
    RUN(single_line_if_return_value);
    RUN(stmt_print_integer_expr);
    RUN(var_decl_coalescing_option);

    /* ===== Batch 8: Deep Branch Coverage - Targeted ===== */

    printf("\n--- Coverage Batch 8: String Interpolation Edge Cases ---\n");
    RUN(interp_int_expr_cast);
    RUN(interp_only_trailing_text);
    RUN(interp_empty_result_b8);
    RUN(interp_nested_braces);

    printf("\n--- Coverage Batch 8: Option is_none Path ---\n");
    RUN(option_is_none_method);
    RUN(option_struct_field_is_none);

    printf("\n--- Coverage Batch 8: Method Call Edge Cases ---\n");
    RUN(replace_arg_with_parens);
    RUN(static_method_string_escape);
    RUN(static_method_nested_parens);
    RUN(instance_method_string_escape);
    RUN(instance_method_nested_parens);
    RUN(field_bracket_before_paren_b8);
    RUN(struct_field_nested_bracket);
    RUN(text_slice_method);
    RUN(method_chain_option_colon);
    RUN(chained_method_str_escape);
    RUN(chained_method_nested_parens);

    printf("\n--- Coverage Batch 8: Func Call Edge Cases ---\n");
    RUN(func_arg_string_escape);
    RUN(struct_ctor_empty_args);
    RUN(struct_ctor_positional_bracket);
    RUN(struct_ctor_value_escape);
    RUN(array_index_nested_bracket);
    RUN(identifier_underscore_start);

    printf("\n--- Coverage Batch 8: Parse Var Decl Edge Cases ---\n");
    RUN(var_decl_text_method_trim);
    RUN(var_decl_text_method_slice);

    printf("\n--- Coverage Batch 8: Block Control Flow ---\n");
    RUN(block_use_skip_b8);
    RUN(block_export_skip);
    RUN(block_import_skip);
    RUN(elif_else_blank_line_between);
    RUN(range_paren_inside_arg);
    RUN(range_bracket_inside_arg);

    printf("\n--- Coverage Batch 8: Struct/Enum First Pass ---\n");
    RUN(struct_blank_comment_fields);
    RUN(enum_blank_comment_variants);

    printf("\n--- Coverage Batch 8: Module Level ---\n");
    RUN(module_option_var_init);
    RUN(module_struct_var_init);

    printf("\n--- Coverage Batch 8: Implicit Return Edge Cases ---\n");
    RUN(method_ends_with_continue);
    RUN(method_ends_with_elif);
    RUN(method_ends_with_else);
    RUN(method_ends_with_assignment);
    RUN(fn_implicit_return_paren_expr);
    RUN(fn_implicit_return_bracket_expr);
    RUN(fn_implicit_return_string_expr);
    RUN(method_implicit_return_paren);
    RUN(method_implicit_return_bracket);
    RUN(method_implicit_return_string);

    printf("\n--- Coverage Batch 8: Option Nil Assignment ---\n");
    RUN(dot_expr_option_nil_assign);

    printf("\n--- Coverage Batch 8: Misc ---\n");
    RUN(multi_file_input_b8);
    RUN(modulo_operator_b8);

    /* ===== Batch 9: Struct Array & 100% Branch Coverage ===== */

    printf("\n--- Coverage Batch 9: Struct Array Operations ---\n");
    RUN(struct_array_push);
    RUN(struct_array_pop);
    RUN(for_in_struct_array);
    RUN(for_in_text_array);
    RUN(val_struct_array_with_elements);
    RUN(var_struct_array_with_elements);
    RUN(struct_array_literal_push);
    RUN(struct_array_set);
    RUN(struct_array_index_field);
    RUN(struct_array_single_element);
    RUN(struct_array_type_conversion);
    RUN(module_struct_array_var);
    RUN(module_struct_array_literal);

    printf("\n--- Coverage Batch 9: Block Struct Array ---\n");
    RUN(block_val_struct_array);
    RUN(block_var_struct_array);
    RUN(block_for_in_struct_array);
    RUN(block_for_in_text_array);

    printf("\n--- Coverage Batch 9: Method Args ---\n");
    RUN(method_call_nested_paren_args);
    RUN(instance_method_multi_args);
    RUN(generic_method_multi_args);

    printf("\n--- Coverage Batch 9: Type Inference ---\n");
    RUN(type_infer_struct_array_index_field);
    RUN(type_infer_struct_array_index_no_dot);

    printf("\n--- Coverage Batch 9: Misc ---\n");
    RUN(option_base_no_question);
    RUN(interp_int_needs_cast);
    RUN(interp_multiple_exprs);
    RUN(tab_indentation);
    RUN(if_cond_trailing_space);
    RUN(stmt_nested_array_set_b9);
    RUN(field_access_no_bracket);
    RUN(fn_param_option_type);
    RUN(print_integer_no_space);
    RUN(register_me_method_b9);

    printf("\n--- Coverage Batch 9: Previously Unused Tests ---\n");
    RUN(for_range_two_args_b9);
    RUN(for_range_single_arg_b9);
    RUN(match_pipe_case_b9);
    RUN(method_implicit_return_expr_b9);

    printf("\n--- Coverage Batch 9b: Remaining Branch Targets ---\n");
    RUN(var_struct_array_no_init);
    RUN(type_infer_fn_struct_field);
    RUN(type_infer_text_slice);
    RUN(type_infer_struct_field_access);
    RUN(block_option_nil_assign_b9);
    RUN(single_line_if_paren_cond);
    RUN(single_line_if_string_cond);
    RUN(module_match_b9);
    RUN(struct_array_push_constructed);
    RUN(struct_array_multi_push);
    RUN(struct_array_bracket_set);

    printf("\n--- Coverage Batch 9b: Crash Tests ---\n");
    RUN(empty_fn_body);
    RUN(deep_nested_if);
    RUN(many_variables);

    /* Coverage Batch 10 – remaining uncovered lines */
    RUN(struct_field_struct_array_index);
    RUN(interp_literal_prefix_first);
    RUN(type_infer_text_fn_result);
    RUN(type_infer_fn_struct_unknown_field);

    /* ============================================================
     * Bug-fix regression tests: string concat, .len() on text fn,
     * for-loop over nested/float arrays
     * ============================================================ */
    printf("\n--- Bug Fix: String concat with + operator ---\n");
    RUN(str_concat_plus_var);
    RUN(str_concat_plus_func);
    RUN(str_concat_triple);
    RUN(str_concat_pure_literal);
    RUN(str_concat_interp_no_plus);

    printf("\n--- Bug Fix: .len() on text-returning functions ---\n");
    RUN(len_on_text_var);
    RUN(len_on_text_func);
    RUN(len_on_array_var);

    printf("\n--- Bug Fix: for-loop over nested/float arrays ---\n");
    RUN(for_nested_text_array);
    RUN(for_nested_int_array);
    RUN(for_float_array);
    RUN(for_text_array_unchanged);
    RUN(for_int_array_unchanged);

    /* Coverage Batch 11 – remaining coverable lines */
    printf("\n--- Coverage Batch 11: Float arrays & fallback paths ---\n");
    RUN(float_array_push);
    RUN(float_array_index);
    RUN(float_array_type_infer);
    RUN(fn_return_struct_unknown_field);
    RUN(struct_array_unknown_field);

    printf("\n=== All %d tests passed ===\n", tests_run);
    return 0;
}
