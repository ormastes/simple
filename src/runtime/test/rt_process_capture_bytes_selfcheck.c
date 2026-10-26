/* Byte-level tests of the REAL runtime_process.c provider and child pipes.
 * A test-only value adapter records exact rt_string_new lengths and owns copies;
 * this isolates the provider without linking another lane's runtime.c changes.
 * It does not qualify the production tagged-value ABI or a Simple compiler.
 */
#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#else
#include <unistd.h>
#include <time.h>
#endif

typedef struct { size_t len; unsigned char bytes[]; } TestString;
static size_t copied_bytes;
static size_t string_allocations;

static void* checked_alloc(size_t size) {
    void* value = calloc(1, size);
    if (!value) { fputs("ERROR allocation failed\n", stderr); exit(2); }
    return value;
}
int64_t rt_value_int(int64_t value) { return value; }
SplArray* rt_array_new(int64_t cap) {
    SplArray* a = checked_alloc(sizeof(*a));
    a->cap = cap;
    a->items = checked_alloc((size_t)cap * sizeof(*a->items));
    return a;
}
int64_t rt_array_len(SplArray* a) { return a ? a->len : 0; }
int64_t rt_array_get(SplArray* a, int64_t i) {
    if (!a || i < 0 || i >= a->len) abort();
    return a->items[i].as_int;
}
int8_t rt_array_push(SplArray* a, int64_t value) {
    if (!a || a->len >= a->cap) abort();
    a->items[a->len++].as_int = value;
    return 1;
}
int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    if (len > SIZE_MAX - sizeof(TestString) - 1) abort();
    TestString* s = checked_alloc(sizeof(*s) + (size_t)len + 1);
    s->len = (size_t)len;
    if (len) memcpy(s->bytes, bytes, (size_t)len);
    copied_bytes += (size_t)len;
    string_allocations++;
    return (int64_t)(uintptr_t)s;
}
const uint8_t* rt_string_data(int64_t value) {
    return ((TestString*)(uintptr_t)value)->bytes;
}
static TestString* stream(SplArray* a, int i) {
    return (TestString*)(uintptr_t)rt_array_get(a, i);
}
static void free_array(SplArray* a, int string_count) {
    for (int i = 0; i < string_count; i++) free(stream(a, i));
    free(a->items);
    free(a);
}
static void write_bytes(FILE* file, const void* bytes, size_t size) {
    if (fwrite(bytes, 1, size, file) != size || fflush(file)) exit(90);
}
static const unsigned char records[] = "R  new name.spl\0old name.spl\0?? next.spl\0";
static const unsigned char binary_out[] = {0, 'a', 0, 'b', 'c', 0, 'd', 0};
static const unsigned char binary_err[] = {'e', 0, 'r', 0};
static const unsigned char over[] = {0, 'a', 0, 'b', 'c', 0, 'd', 0,
    'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 0, 'x', 0, 'y'};

static int child(const char* mode) {
#ifdef _WIN32
    _setmode(_fileno(stdout), _O_BINARY);
    _setmode(_fileno(stderr), _O_BINARY);
#endif
    if (!strcmp(mode, "empty")) return 0;
    if (!strcmp(mode, "text")) {
        write_bytes(stdout, "hello\n", 6); write_bytes(stderr, "warning\n", 8);
        return 7;
    }
    if (!strcmp(mode, "records")) { write_bytes(stdout, records, sizeof(records)-1); return 0; }
    if (!strcmp(mode, "over")) {
        write_bytes(stdout, over, sizeof(over)); write_bytes(stderr, over, sizeof(over));
        return 0;
    }
    if (!strcmp(mode, "bench-text") || !strcmp(mode, "bench-nul")) {
        unsigned char bytes[65536];
        memset(bytes, 'z', sizeof(bytes));
        if (!strcmp(mode, "bench-nul")) {
            /* Late NUL keeps baseline/candidate copied volumes comparable. */
            bytes[sizeof(bytes)-2] = 0;
        }
        write_bytes(stdout, bytes, sizeof(bytes));
        write_bytes(stderr, bytes, sizeof(bytes));
        return 0;
    }
    write_bytes(stdout, binary_out, sizeof(binary_out));
    write_bytes(stderr, binary_err, sizeof(binary_err));
    if (!strcmp(mode, "timeout")) {
#ifdef _WIN32
        Sleep(5000);
#else
        sleep(5);
#endif
    }
    return 0;
}

static SplArray* capture(const char* executable, const char* mode, int64_t limit, int timeout) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, rt_string_new((const uint8_t*)"--child", 7));
    rt_array_push(args, rt_string_new((const uint8_t*)mode, strlen(mode)));
    SplArray* result = limit == -1
        ? (SplArray*)(uintptr_t)rt_process_run_timeout(executable, strlen(executable), args, timeout)
        : rt_process_run_bounded(executable, strlen(executable), args, timeout, limit);
    free_array(args, 2);
    return result;
}
static int exact(TestString* actual, const void* expected, size_t length) {
    return actual->len == length && !memcmp(actual->bytes, expected, length)
        && actual->bytes[length] == 0;
}
static int ended_by(TestString* actual, const char* suffix) {
    size_t n = strlen(suffix);
    return actual->len >= n && !memcmp(actual->bytes + actual->len - n, suffix, n);
}
static int check_over(TestString* actual, size_t limit) {
    unsigned char expected[160];
    size_t head = (limit+1)/2, tail = limit/2;
    memcpy(expected, over, head);
    int marker = snprintf((char*)expected + head, sizeof(expected)-head,
        "\n[output truncated: %zu bytes omitted]\n", sizeof(over)-limit);
    memcpy(expected + head + marker, over + sizeof(over)-tail, tail);
    return exact(actual, expected, head+(size_t)marker+tail);
}

static int failures, cases;
static void record(const char* name, int ok) {
    cases++; failures += !ok;
    printf("CASE %s %s\n", name, ok ? "PASS" : "FAIL");
}
static double seconds(void) {
#ifdef _WIN32
    LARGE_INTEGER now, frequency;
    QueryPerformanceCounter(&now); QueryPerformanceFrequency(&frequency);
    return (double)now.QuadPart / (double)frequency.QuadPart;
#else
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return now.tv_sec + now.tv_nsec / 1e9;
#endif
}
int main(int argc, char** argv) {
    if (argc > 2 && !strcmp(argv[1], "--child")) return child(argv[2]);
    if (argc > 1 && !strcmp(argv[1], "--reset-only")) {
        SplArray* a = capture(argv[0], "binary", 8, 3000);
        int binary_ok = exact(stream(a,0),binary_out,sizeof(binary_out)) && exact(stream(a,1),binary_err,sizeof(binary_err));
        free_array(a,2);
        a = capture(argv[0], "empty", 8, 3000);
        record("nul-then-empty-reset", binary_ok && exact(stream(a,0),"",0) && exact(stream(a,1),"",0));
        free_array(a,2);
        a = capture(argv[0], "text", 16, 3000);
        record("empty-then-text-reset", exact(stream(a,0),"hello\n",6) && exact(stream(a,1),"warning\n",8) && rt_array_get(a,2)==7);
        free_array(a,2);
        return failures ? 1 : 0;
    }
    if (argc > 2 && !strcmp(argv[1], "--bench")) {
        double started = seconds();
        for (int i = 0; i < 20; i++) {
            SplArray* a = capture(argv[0], argv[2], 65536, 3000);
            if (rt_array_get(a, 2) != 0) return 2;
            free_array(a, 2);
        }
        printf("BENCH mode=%s iterations=20 seconds=%.9f string_allocations=%zu copied_bytes=%zu\n",
            argv[2], seconds()-started, string_allocations, copied_bytes);
        return 0;
    }
    SplArray* a = capture(argv[0], "empty", 16, 3000);
    record("empty", exact(stream(a,0), "",0) && exact(stream(a,1),"",0) && rt_array_get(a,2)==0);
    free_array(a,2);
    a = capture(argv[0], "text", 16, 3000);
    record("text-and-exit", exact(stream(a,0),"hello\n",6) && exact(stream(a,1),"warning\n",8) && rt_array_get(a,2)==7);
    free_array(a,2);
    a = capture(argv[0], "records", 128, 3000);
    record("git-nul-records-and-spaces", exact(stream(a,0),records,sizeof(records)-1) && exact(stream(a,1),"",0));
    free_array(a,2);
    a = capture(argv[0], "binary", 8, 3000);
    record("both-streams-nul-and-exact-bound", exact(stream(a,0),binary_out,sizeof(binary_out)) && exact(stream(a,1),binary_err,sizeof(binary_err)));
    free_array(a,2);
    a = capture(argv[0], "binary", -1, 3000);
    record("timeout-api-nul", exact(stream(a,0),binary_out,sizeof(binary_out)) && exact(stream(a,1),binary_err,sizeof(binary_err)));
    free_array(a,2);
    const size_t limits[] = {8, 1, 0};
    for (size_t i=0; i<sizeof(limits)/sizeof(limits[0]); i++) {
        a = capture(argv[0], "over", (int64_t)limits[i], 3000);
        char name[40]; snprintf(name,sizeof(name),"over-bound-%zu",limits[i]);
        record(name, check_over(stream(a,0),limits[i]) && check_over(stream(a,1),limits[i]) && rt_array_get(a,2)==0);
        free_array(a,2);
    }
    a = capture(argv[0], "timeout", 64, 200);
    TestString *out=stream(a,0), *err=stream(a,1);
    record("timeout-keeps-nul-prefix-and-marker", rt_array_get(a,2)==-1 && out->len>=sizeof(binary_out)
        && !memcmp(out->bytes,binary_out,sizeof(binary_out)) && err->len>=sizeof(binary_err)
        && !memcmp(err->bytes,binary_err,sizeof(binary_err))
        && ended_by(err,"[TIMEOUT: Process killed after 200ms]"));
    free_array(a,2);
    a = rt_process_run_bounded("",0,NULL,200,8);
    record("missing-command", rt_array_get(a,2)==-1 && exact(stream(a,0),"",0) && exact(stream(a,1),"missing command",15));
    free_array(a,2);
    a = rt_process_run_bounded(argv[0],strlen(argv[0]),NULL,200,-2);
    record("invalid-bound", rt_array_get(a,2)==-1 && exact(stream(a,0),"",0) && exact(stream(a,1),"",0));
    free_array(a,2);
    printf("RESULT cases=%d failures=%d\n", cases, failures);
    return failures ? 1 : 0;
}
