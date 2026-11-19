/* Non-Windows test: it redirects stderr through a POSIX tmpfile/dup2 pair. */
#if defined(_WIN32)
#include <stdio.h>
int main(void) { puts("SKIP: rt_transient_scope_object_cap_selfcheck is POSIX-only"); return 77; }
#else
/* One transient scope may track any number of objects (Rust-twin parity).
 *
 * Regression: the C runtime refused to grow a scope's tracking list past
 * 2^24 entries, so the next registration failed and rt_core_concat_bytes_v1
 * panicked "text concat: registration failed" (Stage 3 self-build, first
 * staged-codegen batch). The advisory threshold is lowered here so the check
 * crosses it cheaply; the production value is 2^24.
 * doc/08_tracking/bug/stage3_transient_scope_object_cap_panic_2026-11-20.md
 *
 * Build (from repo root):
 *   clang -O1 -w -ffunction-sections -fdata-sections -Wl,--gc-sections -fuse-ld=lld \
 *     -o /tmp/rt_transient_scope_object_cap_selfcheck \
 *     src/runtime/test/rt_transient_scope_object_cap_selfcheck.c -lm -lpthread -ldl
 * Red-evidence variant (pre-fix runtime): -DRT_SCOPE_CAP_CHECK_COUNT=16777280. */
#ifndef RT_CORE_TRANSIENT_SCOPE_WARN_OBJECTS
#define RT_CORE_TRANSIENT_SCOPE_WARN_OBJECTS ((size_t)1024)
#endif
#ifndef RT_SCOPE_CAP_CHECK_COUNT
#define RT_SCOPE_CAP_CHECK_COUNT ((int64_t)RT_CORE_TRANSIENT_SCOPE_WARN_OBJECTS * 3 + 7)
#endif
#include "../runtime_native.c"
#include <unistd.h>

void spl_panic(const char* message) {
    fprintf(stderr, "PANIC: %s\n", message ? message : "");
    fflush(stderr);
    _exit(101);
}

static unsigned checks;
#define CHECK(condition) do { ++checks; if (!(condition)) { \
    fprintf(stdout, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; \
} } while (0)

static int count_warnings(FILE* captured) {
    char line[512];
    int warnings = 0;
    rewind(captured);
    while (fgets(line, sizeof line, captured)) {
        if (strstr(line, "[transient-scope] WARNING")) warnings++;
    }
    return warnings;
}

/* Registers `count` concatenated strings inside one scope; returns 0 on
 * success. Every registration goes through rt_core_concat_bytes_v1, the
 * owner that panicked in the incident. */
static int fill_one_scope(int64_t count) {
    const int64_t left = rt_string_new((const uint8_t*)"ab", 2);
    const int64_t right = rt_string_new((const uint8_t*)"cd", 2);
    CHECK(left != rt_core_nil() && right != rt_core_nil());
    const int64_t registry_before = rt_heap_registry_count();
    CHECK(rt_transient_array_scope_begin());
    for (int64_t i = 0; i < count; i++) {
        CHECK(rt_string_concat(left, right) != rt_core_nil());
    }
    CHECK(rt_heap_registry_count() - registry_before == count);
    CHECK(rt_transient_array_scope_end());
    /* Scope end reclaims every tracked object, past the threshold too. */
    CHECK(rt_heap_registry_count() == registry_before);
    return 0;
}

/* Generalization: the same list tracks arrays, dicts, enums, floats and
 * closures (rt_core_register_scoped_immortal); arrays and boxed floats must
 * cross the threshold just like strings. */
static int fill_mixed_one_scope(int64_t count) {
    const int64_t registry_before = rt_heap_registry_count();
    CHECK(rt_transient_array_scope_begin());
    for (int64_t i = 0; i < count; i++) {
        CHECK(rt_array_new(0) != NULL);
        CHECK(rt_value_float(0.5 + (double)i) != rt_core_nil());
    }
    CHECK(rt_transient_array_scope_end());
    CHECK(rt_heap_registry_count() == registry_before);
    return 0;
}

int main(void) {
    FILE* captured = tmpfile();
    CHECK(captured != NULL);
    fflush(stderr);
    const int saved_stderr = dup(STDERR_FILENO);
    CHECK(saved_stderr >= 0);
    CHECK(dup2(fileno(captured), STDERR_FILENO) >= 0);

    const int first = fill_one_scope(RT_SCOPE_CAP_CHECK_COUNT);
    fflush(stderr);
    const int warnings_first = count_warnings(captured);
    /* A second over-threshold scope warns again (one line per scope). */
    const int second = first == 0 ? fill_one_scope(RT_SCOPE_CAP_CHECK_COUNT) : 1;
    fflush(stderr);
    const int warnings_total = count_warnings(captured);
    const int mixed = second == 0 ? fill_mixed_one_scope(RT_SCOPE_CAP_CHECK_COUNT) : 1;
    fflush(stderr);
    const int warnings_mixed = count_warnings(captured);

    dup2(saved_stderr, STDERR_FILENO);
    close(saved_stderr);
    CHECK(first == 0);
    CHECK(second == 0);
    CHECK(mixed == 0);
    if ((size_t)RT_SCOPE_CAP_CHECK_COUNT > RT_CORE_TRANSIENT_SCOPE_WARN_OBJECTS) {
        CHECK(warnings_first == 1);
        CHECK(warnings_total == 2);
        CHECK(warnings_mixed == 3);
    }
    /* An under-threshold scope stays silent. */
    CHECK(fill_one_scope((int64_t)RT_CORE_TRANSIENT_SCOPE_WARN_OBJECTS / 2) == 0);
    printf("rt_transient_scope_object_cap_selfcheck: PASS (%u checks, %lld objects per scope)\n",
           checks, (long long)RT_SCOPE_CAP_CHECK_COUNT);
    return 0;
}
#endif
