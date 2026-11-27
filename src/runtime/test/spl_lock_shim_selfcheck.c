/* Selfcheck for src/runtime/spl_lock_shim.h: init/lock/unlock/wait/signal/
 * broadcast/destroy on both Win32 and POSIX. Run by
 * scripts/check/check-spl-lock-shim-selfcheck.shs (clang only, plus
 * ASan/UBSan and TSan variants). Prints "PASS: <n> checks" and exits 0. */
#include <stdio.h>
#include <stdlib.h>

#if defined(_WIN32) || defined(_WIN64)
#include <windows.h>
typedef HANDLE th_t;
static DWORD WINAPI th_tramp(LPVOID p);
#else
#include <pthread.h>
typedef pthread_t th_t;
static void* th_tramp(void* p);
#endif
#include "spl_lock_shim.h"

#define WAITERS 4
#define ITEMS 2000

static spl_lk_mutex g_m;
static spl_lk_cond g_c;
static int g_queue;      /* produced, not yet consumed */
static int g_consumed;
static int g_gate;       /* broadcast phase */
static int g_passed;     /* waiters released through the gate */
static int checks, fails;

static void check(int ok, const char* what) {
    checks++;
    if (!ok) { fails++; fprintf(stderr, "FAIL: %s\n", what); }
}

static void consumer(void) {
    for (int i = 0; i < ITEMS; i++) {
        spl_lk_lock(&g_m);
        while (g_queue == 0) spl_lk_wait(&g_c, &g_m);
        g_queue--;
        g_consumed++;
        spl_lk_unlock(&g_m);
    }
}

static void gate_waiter(void) {
    spl_lk_lock(&g_m);
    while (!g_gate) spl_lk_wait(&g_c, &g_m);
    g_passed++;
    spl_lk_unlock(&g_m);
}

typedef void (*fn_t)(void);
#if defined(_WIN32) || defined(_WIN64)
static DWORD WINAPI th_tramp(LPVOID p) { ((fn_t)p)(); return 0; }
static th_t th_start(fn_t f) { return CreateThread(NULL, 0, th_tramp, (LPVOID)f, 0, NULL); }
static void th_join(th_t t) { WaitForSingleObject(t, INFINITE); CloseHandle(t); }
#else
static void* th_tramp(void* p) { ((fn_t)p)(); return NULL; }
static th_t th_start(fn_t f) { th_t t; if (pthread_create(&t, NULL, th_tramp, (void*)f) != 0) abort(); return t; }
static void th_join(th_t t) { pthread_join(t, NULL); }
#endif

int main(void) {
    spl_lk_init(&g_m, &g_c);

    /* signal: one producer, one consumer, every item delivered exactly once */
    th_t c = th_start(consumer);
    for (int i = 0; i < ITEMS; i++) {
        spl_lk_lock(&g_m);
        g_queue++;
        spl_lk_signal(&g_c);
        spl_lk_unlock(&g_m);
    }
    th_join(c);
    check(g_consumed == ITEMS, "signal: all items consumed");
    check(g_queue == 0, "signal: queue drained");

    /* broadcast: one wake releases every waiter */
    th_t w[WAITERS];
    for (int i = 0; i < WAITERS; i++) w[i] = th_start(gate_waiter);
    spl_lk_lock(&g_m);
    g_gate = 1;
    spl_lk_broadcast(&g_c);
    spl_lk_unlock(&g_m);
    for (int i = 0; i < WAITERS; i++) th_join(w[i]);
    check(g_passed == WAITERS, "broadcast: all waiters released");

    /* lock/unlock re-entry after destroy+re-init */
    spl_lk_destroy(&g_m, &g_c);
    spl_lk_init(&g_m, &g_c);
    spl_lk_lock(&g_m);
    spl_lk_unlock(&g_m);
    check(1, "re-init lock/unlock");
    spl_lk_destroy(&g_m, &g_c);

    if (fails) { printf("FAIL: %d checks, %d failures\n", checks, fails); return 1; }
    printf("PASS: %d checks, 0 failures\n", checks);
    return 0;
}
