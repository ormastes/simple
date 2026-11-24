/* Selfcheck: untagged RtCoreString.data pointers (produced by rt_interp_cstr
 * on [text] element reads and Option/Result<text,_> unwraps) must retain their
 * counted length across embedded NUL bytes in rt_strcat_tagged, rt_strsplit,
 * rt_array_join_any, rt_text_eq_any, rt_text_cmp_any, rt_text_to_bytes, and
 * rt_string_* operations.
 *
 * Build/run:
 *   clang -O1 -w -I src/runtime -Wl,-dead_strip -o /tmp/rt_nul_ops \
 *     src/runtime/test/rt_text_data_pointer_nul_ops_selfcheck.c src/runtime/runtime.c \
 *     libspl_hosted_runtime.a -lsqlite3 -lm -lpthread -ldl && /tmp/rt_nul_ops
 */
#include "../runtime_native.c"
#include <assert.h>

int main(void) {
    /* 1. Exact P3a->P3b HirCodecWriter.put_text reproduction: "\0" + "\n". */
    static const uint8_t nul_one[1] = {0};
    static const uint8_t nl_one[1] = {'\n'};
    int64_t nul_tagged = rt_string_new(nul_one, 1);
    int64_t nl_tagged = rt_string_new(nl_one, 1);
    int64_t nul_raw = (int64_t)(uintptr_t)rt_interp_cstr(nul_tagged);
    int64_t nl_raw = (int64_t)(uintptr_t)rt_interp_cstr(nl_tagged);

    int64_t cat = rt_strcat_tagged(nul_raw, nl_raw);
    assert(rt_string_len(cat) == 2);
    const uint8_t* cat_data = rt_string_data(cat);
    assert(cat_data != NULL && cat_data[0] == 0 && cat_data[1] == '\n');

    /* 2. Exact FlatPoolReader .fpc/.hir line-split reproduction: "admitted\n\0\ncontains". */
    static const uint8_t fpc_bytes[19] = {
        'a','d','m','i','t','t','e','d','\n',
        0, '\n',
        'c','o','n','t','a','i','n','s'
    };
    int64_t fpc_tagged = rt_string_new(fpc_bytes, sizeof(fpc_bytes));
    const char* fpc_cstr = rt_interp_cstr(fpc_tagged);
    SplArray* lines = rt_strsplit(fpc_cstr, "\n");
    assert(lines != NULL);
    assert(rt_array_len(lines) == 3);
    assert(rt_string_len(rt_array_get(lines, 0)) == 8);
    assert(rt_string_len(rt_array_get(lines, 1)) == 1);
    assert(rt_string_data(rt_array_get(lines, 1))[0] == 0);
    assert(rt_string_len(rt_array_get(lines, 2)) == 8);

    /* 3. rt_string_split / contains / starts_with / ends_with / trim on data pointer. */
    int64_t fpc_raw = (int64_t)(uintptr_t)fpc_cstr;
    int64_t split_tagged = rt_string_split(fpc_raw, nl_raw);
    assert(rt_array_len((SplArray*)(uintptr_t)split_tagged) == 3);
    assert(rt_string_contains(fpc_raw, nul_raw) == 1);
    assert(rt_string_starts_with(cat, nul_raw) == 1);
    /* P4 closure scanner passes the unboxed result of removing "use ". */
    static const char lazy_import[] = "use lazy app.cli.doc_links.{doc_links_command_v1}";
    int64_t bare_tail = (int64_t)(uintptr_t)(lazy_import + 4);
    int64_t lazy_prefix = rt_string_new((const uint8_t*)"lazy ", 5);
    assert(rt_string_starts_with(bare_tail, lazy_prefix) == 1);
    assert(rt_string_starts_with(lazy_prefix, (int64_t)(uintptr_t)"lazy") == 1);
    assert(rt_string_starts_with(bare_tail, nul_raw) == 0);
    assert(rt_string_starts_with((int64_t)(uintptr_t)"la", lazy_prefix) == 0);
    assert(rt_string_starts_with((int64_t)(uintptr_t)"", (int64_t)(uintptr_t)"") == 1);
    assert(rt_string_starts_with(3, (int64_t)(uintptr_t)"") == 0);
    assert(rt_string_ends_with(cat, nl_raw) == 1);
    int64_t trimmed = rt_string_trim((int64_t)(uintptr_t)rt_interp_cstr(cat));
    assert(rt_string_len(trimmed) == 1);
    assert(rt_string_data(trimmed)[0] == 0);

    /* 4. rt_text_eq_any & rt_text_cmp_any distinguish suffixes after embedded NUL. */
    static const uint8_t ax[3] = {'a', 0, 'x'};
    static const uint8_t ay[3] = {'a', 0, 'y'};
    int64_t ax_raw = (int64_t)(uintptr_t)rt_interp_cstr(rt_string_new(ax, 3));
    int64_t ay_raw = (int64_t)(uintptr_t)rt_interp_cstr(rt_string_new(ay, 3));
    assert(rt_text_eq_any(ax_raw, ay_raw) == 0);
    assert(rt_text_eq_any(ax_raw, ax_raw) == 1);
    assert(rt_text_cmp_any(ax_raw, ay_raw) < 0);

    /* 5. rt_array_join_any & rt_text_to_bytes preserve embedded NUL bytes. */
    SplArray* join_in = rt_array_new(2);
    rt_array_push(join_in, ax_raw);
    rt_array_push(join_in, ay_raw);
    int64_t joined = rt_array_join_any((int64_t)(uintptr_t)join_in, nul_raw);
    assert(rt_string_len(joined) == 7);

    int64_t byte_arr = rt_text_to_bytes(ax_raw);
    assert(rt_array_len((SplArray*)(uintptr_t)byte_arr) == 3);

    /* 6. Polymorphic int/any guards still ignore untagged data pointers. */
    assert(rt_to_int_dynamic(4097) == 4097);
    assert(rt_value_as_int(16) == 2);

    printf("PASS rt_text_data_pointer_nul_ops_selfcheck\n");
    return 0;
}
