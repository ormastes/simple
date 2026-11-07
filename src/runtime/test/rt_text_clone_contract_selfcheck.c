/* Actual runtime owners, with compile-time-only allocation/registration faults.
 * The panic stub makes the owner's nonreturning failure observable as exit 101;
 * this does not qualify the language unwinder or bootstrap compiler. */
#define RT_STRING_CONCAT_TESTING 1
#include "../runtime_native.c"
#include <sys/wait.h>

static int64_t expected_registry = -1;
void spl_panic(const char* message) {
    if (expected_registry >= 0 && rt_heap_registry_count() != expected_registry)
        _exit(102);
    fprintf(stderr, "%s\n", message);
    fflush(stderr);
    _exit(101);
}

static unsigned checks;
#define CHECK(condition) do { ++checks; if (!(condition)) { \
    fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; \
} } while (0)

static int64_t concat(int route, int64_t left, int64_t right) {
    return route ? rt_strcat_tagged(left, right) : rt_string_concat(left, right);
}

static int text_is(int64_t text, const uint8_t* bytes, size_t length) {
    const uint8_t* actual = rt_string_data(text);
    return actual && rt_string_len(text) == (int64_t)length &&
        memcmp(actual, bytes, length) == 0 && actual[length] == 0;
}

static int expect_failure(int route, int fault, const char* expected) {
    int fds[2];
    if (pipe(fds)) return 0;
    pid_t child = fork();
    if (child < 0) { close(fds[0]); close(fds[1]); return 0; }
    if (!child) {
        close(fds[0]);
        if (dup2(fds[1], STDERR_FILENO) < 0) _exit(103);
        close(fds[1]);
        int64_t left = rt_string_new((const uint8_t*)"left", 4);
        int64_t right = rt_string_new((const uint8_t*)"right", 5);
        expected_registry = rt_heap_registry_count();
        if (fault <= 2) rt_concat_test_fault_v1 = fault;
        else {
            RtCoreString* source = rt_core_as_string(left);
            if (!source) _exit(104);
            source->len = fault == 3 ? UINT64_MAX : SIZE_MAX - sizeof(RtCoreString);
            if (fault == 4) rt_core_as_string(right)->len = 0;
        }
        (void)concat(route, left, right);
        _exit(105); /* Nil or another returned value is not an infallible success. */
    }
    close(fds[1]);
    char message[256] = {0};
    size_t used = 0;
    ssize_t count;
    while (used < sizeof(message) - 1 &&
           (count = read(fds[0], message + used, sizeof(message) - 1 - used)) > 0)
        used += (size_t)count;
    close(fds[0]);
    int status;
    if (waitpid(child, &status, 0) != child) return 0;
    return WIFEXITED(status) && WEXITSTATUS(status) == 101 &&
        strcmp(message, expected) == 0;
}

int main(void) {
    const uint8_t bytes[] = {'A', 0, 'Z', 0xf0, 0x9f, 0x98, 0x80};
    int64_t empty = rt_string_new((const uint8_t*)"", 0);
    for (int route = 0; route < 2; ++route) {
        int64_t source = rt_string_new(bytes, sizeof(bytes));
        int64_t cloned = concat(route, source, empty);
        CHECK(cloned != source && text_is(cloned, bytes, sizeof(bytes)));
        CHECK(rt_string_free(source) == 1);
        CHECK(text_is(cloned, bytes, sizeof(bytes)));
        CHECK(rt_string_free(cloned) == 1);
        int64_t blank = concat(route, empty, empty);
        CHECK(text_is(blank, (const uint8_t*)"", 0));
        CHECK(rt_string_free(blank) == 1);
        CHECK(expect_failure(route, 1, "text concat: allocation failed\n"));
        CHECK(expect_failure(route, 2, "text concat: registration failed\n"));
        CHECK(expect_failure(route, 3, "text concat: length overflow\n"));
        CHECK(expect_failure(route, 4, "text concat: allocation size overflow\n"));
    }
    int64_t raw = rt_strcat_tagged((int64_t)(uintptr_t)"raw", empty);
    CHECK(text_is(raw, (const uint8_t*)"raw", 3));
    CHECK(rt_string_free(raw) == 1);
    int64_t nil = rt_strcat_tagged(rt_value_nil(), empty);
    CHECK(text_is(nil, (const uint8_t*)"", 0));
    CHECK(rt_string_free(nil) == 1);
    const uint8_t za[] = {'a', 0, 'z'}, aa[] = {'a', 0, 'a'};
    int64_t z = rt_string_new(za, sizeof(za)), a = rt_string_new(aa, sizeof(aa));
    CHECK(rt_text_cmp_any(z, a) > 0);
    CHECK(rt_text_cmp_any(a, z) < 0);
    CHECK(rt_text_cmp_any(z, z) == 0);
    CHECK(rt_text_cmp_any(a, (int64_t)(uintptr_t)"a") > 0);
    CHECK(rt_text_cmp_any((int64_t)(uintptr_t)"a", a) < 0);
    CHECK(rt_text_cmp_any(rt_value_nil(), empty) == 0);
    CHECK(rt_string_free(z) == 1 && rt_string_free(a) == 1);
    printf("TEXT_CLONE_CONTRACT_PASS checks=%u\n", checks);
    return 0;
}
