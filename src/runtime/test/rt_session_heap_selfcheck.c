/* Build session heap (BSM T1) self-check.
 *
 * doc/05_design/compiler/memory/build_session_memory_model_v1.md §3-§4, P1.
 * The core-C bootstrap runtime capsule compiles and runs this check.
 *   (a) session allocations outside a module scope are freed at session end;
 *   (b) inside a module scope: unadopted objects die at module end, adopted
 *       ones survive until session end;
 *   (c) adopt prunes (I2) and session containers grow under the session
 *       allocator (I3): adopting the session-owned OUTER array visits O(1)
 *       nodes however many rows it holds (N=2000);
 *   (d) promote with no session keeps the legacy permanent retag;
 *   (e) refusals return 0 (incl. a foreign thread ending the session).
 */
#if defined(_WIN32)
#include <windows.h>
#else
#include <pthread.h>
#endif
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "../runtime.h"

extern uint64_t spl_session_adopt_visits_debug(void);

static int failures = 0;

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

/* RtCoreArray.transient_scope_id: ABI-frozen offset 4 (design I6). */
static uint32_t array_tag(SplArray* array) {
    uint32_t tag;
    /* SplArray* is a tagged heap value: strip the low tag bits first. */
    const uint8_t* header = (const uint8_t*)((uintptr_t)array & ~(uintptr_t)7);
    memcpy(&tag, header + 4, sizeof(tag));
    return tag;
}

static int64_t as_value(SplArray* array) {
    return (int64_t)(uintptr_t)array;
}

static SplArray* make_row(int width) {
    SplArray* row = rt_array_new(width);
    for (int k = 0; k < width; k++) {
        SplArray* leaf = rt_array_new(1);
        rt_array_push(leaf, rt_value_int(k));
        rt_array_push(row, as_value(leaf));
    }
    return row;
}

static void check_session_outside_module(void) {
    int64_t base = rt_heap_registry_count();
    uint32_t s = rt_session_heap_begin();
    check(s != 0 && rt_session_heap_id() == s, "(a) session begins and reports its id");
    SplArray* row = make_row(4);
    const char* bytes = "session-owned text outside any module scope";
    int64_t text = rt_string_new((const uint8_t*)bytes, (int64_t)strlen(bytes));
    rt_array_push(row, text);
    check(array_tag(row) == s, "(a) allocation outside a module scope is session-tagged");
    check(rt_heap_registry_count() == base + 6, "(a) six objects registered");
    check(rt_session_heap_end(s) == 1, "(a) session ends");
    check(rt_heap_registry_count() == base, "(a) session end freed every session object");
    check(rt_session_heap_id() == 0, "(a) no live session after end");
    uint32_t again = rt_session_heap_begin();
    check(again != 0 && again != s, "(a) begin works again after end");
    check(rt_session_heap_end(again) == 1, "(a) second session ends");
}

static void check_module_inside_session(void) {
    int64_t base = rt_heap_registry_count();
    uint32_t s = rt_session_heap_begin();
    check(rt_transient_array_scope_begin() == 1, "(b) module scope begins inside session");
    SplArray* kept = make_row(3);
    SplArray* dropped = make_row(3);
    const char* bytes = "module text adopted into the session";
    int64_t text = rt_string_new((const uint8_t*)bytes, (int64_t)strlen(bytes));
    rt_array_push(kept, text);
    uint32_t module_tag = array_tag(kept);
    check(module_tag != 0 && module_tag != s, "(b) module allocation carries the module tag");
    check(rt_transient_array_scope_pause() == 1, "(b) module scope pauses");
    SplArray* paused = rt_array_new(1);
    check(array_tag(paused) == s, "(b) paused-module allocation goes to the session, not 0");
    check(rt_transient_heap_adopt(as_value(kept)) == 1, "(b) adopt succeeds");
    check(rt_transient_heap_adopt(as_value(kept)) == 1, "(b) adopt is idempotent");
    check(array_tag(kept) == s, "(b) adopted root retagged to the session");
    check(rt_transient_array_scope_end() == 1, "(b) module scope ends");
    check(rt_heap_registry_count() == base + 4 + 1 + 1,
          "(b) module end freed the unadopted row (4) and kept adopted row (4) + text + paused");
    check(rt_array_len(kept) == 4 && rt_string_len(text) == (int64_t)strlen(bytes),
          "(b) adopted graph readable after module end");
    (void)dropped;
    check(rt_session_heap_end(s) == 1, "(b) session ends");
    check(rt_heap_registry_count() == base, "(b) session end freed the adopted graph");
}

static double now_ms(void) {
    return (double)clock() * 1000.0 / CLOCKS_PER_SEC;
}

static void check_adopt_prunes(void) {
    const int rows = 2000;
    int64_t base = rt_heap_registry_count();
    uint32_t s = rt_session_heap_begin();
    SplArray* outer = rt_array_new(0);
    check(array_tag(outer) == s, "(c) outer array is session-owned");
    int all_ok = 1;
    uint64_t max_outer_visits = 0;
    uint64_t row_visits = 0;
    double start = now_ms();
    for (int i = 0; i < rows && all_ok; i++) {
        all_ok = rt_transient_array_scope_begin() == 1;
        SplArray* row = make_row(50);
        all_ok = all_ok && rt_transient_array_scope_pause() == 1;
        all_ok = all_ok && rt_transient_heap_adopt(as_value(row)) == 1; /* adopt BEFORE publish (I1) */
        row_visits = spl_session_adopt_visits_debug();
        all_ok = all_ok && rt_session_alloc_begin() == 1;
        rt_array_push(outer, as_value(row));
        all_ok = all_ok && rt_session_alloc_end() == 1;
        all_ok = all_ok && array_tag(outer) == s && array_tag(row) == s;
        all_ok = all_ok && rt_transient_heap_adopt(as_value(outer)) == 1;
        if (spl_session_adopt_visits_debug() > max_outer_visits) {
            max_outer_visits = spl_session_adopt_visits_debug();
        }
        all_ok = all_ok && rt_transient_array_scope_end() == 1;
    }
    double elapsed = now_ms() - start;
    check(all_ok, "(c) 2000 module scopes adopt + publish under the session allocator");
    check(rt_array_len(outer) == rows, "(c) outer holds every published row");
    check(row_visits == 51, "(c) adopting a row visits row + 50 leaves");
    check(max_outer_visits == 1, "(c) adopting the session-owned outer array visits 1 node (I2 prune)");
    check(rt_heap_registry_count() == base + 1 + (int64_t)rows * 51,
          "(c) every adopted row survived its module scope");
    if (getenv("BSM_SELFCHECK_TIMING")) printf("  info adopt-pattern rows=%d wall_ms=%.0f max_outer_visits=%llu row_visits=%llu\n",
           rows, elapsed, (unsigned long long)max_outer_visits, (unsigned long long)row_visits);
    check(rt_session_heap_end(s) == 1, "(c) session ends");
    check(rt_heap_registry_count() == base, "(c) session end freed outer + all rows in one sweep");
}

static void check_promote_without_session(void) {
    check(rt_session_heap_id() == 0, "(d) no session live");
    check(rt_transient_array_scope_begin() == 1, "(d) module scope begins");
    SplArray* row = make_row(2);
    check(rt_transient_array_scope_pause() == 1, "(d) module scope pauses");
    SplArray* paused = rt_array_new(1);
    check(array_tag(paused) == 0, "(d) paused allocation without session is permanent (tag 0)");
    check(rt_transient_heap_promote(as_value(row)) == 1, "(d) legacy promote succeeds");
    check(array_tag(row) == 0, "(d) legacy promote retags to 0");
    check(rt_transient_array_scope_end() == 1, "(d) module scope ends");
    check(rt_array_len(row) == 2, "(d) promoted row survives");
    rt_array_free(paused);
}

#if defined(_WIN32)
static DWORD WINAPI foreign_end(LPVOID arg) {
    uint32_t s = *(uint32_t*)arg;
    *(uint32_t*)arg = (uint32_t)rt_session_heap_end(s);
    return 0;
}

static int run_foreign_end(uint32_t* session) {
    HANDLE worker = CreateThread(NULL, 0, foreign_end, session, 0, NULL);
    if (!worker) return 0;
    WaitForSingleObject(worker, INFINITE);
    CloseHandle(worker);
    return 1;
}
#else
static void* foreign_end(void* arg) {
    uint32_t s = *(uint32_t*)arg;
    *(uint32_t*)arg = (uint32_t)rt_session_heap_end(s);
    return NULL;
}

static int run_foreign_end(uint32_t* session) {
    pthread_t worker;
    return pthread_create(&worker, NULL, foreign_end, session) == 0 &&
        pthread_join(worker, NULL) == 0;
}
#endif

static void check_refusals(void) {
    check(rt_session_heap_end(0) == 0, "(e) end(0) refused");
    check(rt_session_alloc_begin() == 0, "(e) alloc_begin without session refused");
    check(rt_session_alloc_end() == 0, "(e) alloc_end without session refused");
    check(rt_transient_heap_adopt(rt_value_int(1)) == 0, "(e) adopt without session refused");
    uint32_t s = rt_session_heap_begin();
    check(s != 0, "(e) session begins");
    check(rt_session_heap_begin() == 0, "(e) second live session refused");
    check(rt_session_heap_end(s + 1) == 0, "(e) end of a non-live id refused");
    check(rt_session_alloc_end() == 0, "(e) unbalanced alloc_end refused");
    check(rt_transient_heap_adopt(rt_value_int(1)) == 0, "(e) adopt without a module scope refused");
    check(rt_transient_array_scope_begin() == 1, "(e) module scope begins");
    check(rt_transient_heap_adopt(rt_value_int(1)) == 0, "(e) adopt in a running module scope refused");
    check(rt_session_heap_end(s) == 0, "(e) session end refused while a module scope is active");
    check(rt_transient_array_scope_end() == 1, "(e) module scope ends");
    uint32_t foreign = s;
    check(run_foreign_end(&foreign) && foreign == 0,
          "(e) a foreign thread cannot end this thread's session");
    check(rt_session_heap_end(s) == 1, "(e) owner ends its session");
    check(rt_transient_array_scope_begin() == 1, "(e) module scope begins without session");
    check(rt_session_heap_begin() == 0, "(e) session begin refused while a module scope is active");
    check(rt_transient_array_scope_end() == 1, "(e) module scope ends");
}

int main(void) {
    check_session_outside_module();
    check_module_inside_session();
    check_adopt_prunes();
    check_promote_without_session();
    check_refusals();
    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
