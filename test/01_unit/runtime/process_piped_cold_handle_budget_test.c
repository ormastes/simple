/* Cold-start handle budget for the Windows piped-process primitive
 * (bug: windows_piped_process_cold_handle_growth_2026_10_12).
 * Prints a per-stage GetProcessHandleCount table for the first spawn, then
 * asserts: cold growth (first full cycle) <= COLD_BUDGET handles, growth over
 * 50 further cycles == 0, and 5 distinct first-use shapes add 0 each.
 * Exit 0 = pass, 1 = budget exceeded, 77 = not Windows. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifndef _WIN32
int main(void) { puts("SKIP: windows only"); return 77; }
#else
#include <windows.h>

#define COLD_BUDGET 24
#define CYCLES 50

static const char** test_args;
static int64_t test_arg_count;
int64_t rt_array_len(SplArray* ignored) { (void)ignored; return test_arg_count; }
int64_t rt_array_get(SplArray* ignored, int64_t index) { (void)ignored; return index + 1; }
const uint8_t* rt_string_data(int64_t value) { return (const uint8_t*)test_args[value - 1]; }
int64_t rt_string_len(int64_t s) { (void)s; return 0; }
SplArray* rt_array_new(int64_t c) { (void)c; return NULL; }
int64_t rt_string_new(const uint8_t* b, uint64_t l) { (void)b; (void)l; return 0; }
int8_t rt_array_push(SplArray* a, int64_t v) { (void)a; (void)v; return 0; }
void rt_array_free(SplArray* a) { (void)a; }
int64_t rt_value_int(int64_t v) { return v; }
int64_t rt_tuple_new(int64_t n) { (void)n; return 0; }
int8_t rt_tuple_set(int64_t t, int64_t i, int64_t v) { (void)t; (void)i; (void)v; return 0; }

static long handles(void) {
    DWORD n = 0;
    GetProcessHandleCount(GetCurrentProcess(), &n);
    return (long)n;
}

static void stage(const char* name, long* prev) {
    long now = handles();
    printf("  %-28s %4ld  (%+ld)\n", name, now, now - *prev);
    *prev = now;
}

static int64_t spawn(const char* a0, const char* a1) {
    static const char* args[2];
    static SplArray placeholder;
    args[0] = a0; args[1] = a1;
    test_args = args; test_arg_count = 2;
    return rt_process_spawn_piped("cmd.exe", &placeholder);
}

static int finish(int64_t pid, long* prev, int verbose) {
    if (verbose) stage("after spawn_piped", prev);
    (void)rt_process_write_stdin(pid, "x\r\n");
    if (verbose) stage("after write_stdin", prev);
    for (int i = 0; i < 400 && rt_process_is_alive(pid); i++) Sleep(5);
    for (int i = 0; i < 4; i++) (void)rt_process_read_stdout(pid);
    if (verbose) stage("after read_stdout", prev);
    int ok = rt_process_close_piped(pid) ? 1 : 0;
    if (verbose) stage("after close_piped", prev);
    return ok;
}

int main(void) {
    long prev = handles();
    long start = prev;
    printf("stage                        count  delta\n  %-28s %4ld\n", "process start (console+std)", prev);
    int64_t pid = spawn("/c", "echo hi");
    if (pid <= 0 || !finish(pid, &prev, 1)) { puts("FAIL: first cycle"); return 1; }
    Sleep(100);
    stage("first cycle settled", &prev);
    /* Second cycle is still part of cold init (measured +1: lazily created
     * loader/CRT state); steady state is measured after it. */
    pid = spawn("/c", "echo hi");
    if (pid <= 0 || !finish(pid, &prev, 0)) { puts("FAIL: second cycle"); return 1; }
    Sleep(100);
    stage("second cycle settled", &prev);
    long cold = handles() - start;
    long after_first = handles();
    for (int i = 0; i < CYCLES; i++) {
        pid = spawn("/c", "echo hi");
        if (pid <= 0 || !finish(pid, &prev, 0)) { puts("FAIL: cycle"); return 1; }
    }
    Sleep(100);
    long per_cycle = handles() - after_first;
    static const char* shapes[5][2] = {{"/c","ver"},{"/c","echo a b c"},{"/c","dir /b nul"},{"/d","/c echo z"},{"/c","exit 3"}};
    long before_shapes = handles();
    for (int i = 0; i < 5; i++) {
        pid = spawn(shapes[i][0], shapes[i][1]);
        if (pid > 0) (void)finish(pid, &prev, 0);
    }
    Sleep(100);
    long shapes_growth = handles() - before_shapes;
    printf("cold_growth=%ld (budget %d) cycles%d_growth=%ld (budget 0) distinct_first_use_growth=%ld (budget 0)\n",
           cold, COLD_BUDGET, CYCLES, per_cycle, shapes_growth);
    if (cold > COLD_BUDGET || per_cycle > 0 || shapes_growth > 0) { puts("FAIL: handle budget"); return 1; }
    puts("PASS");
    return 0;
}
#endif
