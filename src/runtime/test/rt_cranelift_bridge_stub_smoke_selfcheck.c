/* Portable smoke check for runtime_cranelift_bridge_stub.c (Windows + POSIX).
 *
 * The POSIX-only rt_cranelift_bridge_stub_named_trap_selfcheck.c uses fork();
 * this check re-executes itself instead, so it also runs on Windows, where
 * the phase-3 stage3 link (2026-11-02) needed the stub file that the baked
 * core-C runtime list omitted.
 *
 * Contract checked (see the stub file header): every symbol EXISTS at link
 * time, and calling one is a NAMED LOUD TRAP -- the process terminates with
 * a nonzero status and stderr names the exact symbol plus "NAMED TRAP". The
 * coded sentinels (0 / -1) after rt_trap_unimplemented() are unreachable, so
 * "returns its documented error code" means "never returns a value".
 *
 * Build + run (clang + lld only; Windows = llvm-mingw UCRT):
 *   clang -std=gnu11 -O1 -fuse-ld=lld -o build/cl_smoke.exe \
 *      src/runtime/test/rt_cranelift_bridge_stub_smoke_selfcheck.c \
 *      src/runtime/runtime_cranelift_bridge_stub.c <core-C runtime archive>
 *   build/cl_smoke.exe
 */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#define SMOKE_POPEN _popen
#define SMOKE_PCLOSE _pclose
#else
#define SMOKE_POPEN popen
#define SMOKE_PCLOSE pclose
#endif

extern int64_t rt_cranelift_new_module(int64_t name_ptr, int64_t name_len, int64_t target);
extern int64_t rt_cranelift_finalize_module(int64_t module);
extern void    rt_cranelift_free_module(int64_t module);
extern int64_t rt_cranelift_fconst(int64_t ctx, int64_t type_, double value);
extern int64_t rt_cranelift_bconst(int64_t ctx, bool value);
extern int64_t spl_cranelift_new_aot_module_config_v2(int64_t name_ptr, int64_t name_len,
        int64_t target_ptr, int64_t target_len, int64_t cpu_ptr, int64_t cpu_len,
        int64_t opt_level, int64_t features_ptr, int64_t features_len);
extern int64_t spl_cranelift_aot_isa_feature_v2(int64_t module, int64_t feature_ptr, int64_t feature_len);
extern int64_t spl_cranelift_aot_opt_level_v2(int64_t module);

typedef struct { const char* name; void (*call)(void); const void* addr; } StubCase;

static void call_new_module(void) { (void)rt_cranelift_new_module(0, 0, 0); }
static void call_finalize(void) { (void)rt_cranelift_finalize_module(0); }
static void call_free(void) { rt_cranelift_free_module(0); }
static void call_fconst(void) { (void)rt_cranelift_fconst(0, 0, 1.5); }
static void call_bconst(void) { (void)rt_cranelift_bconst(0, true); }
static void call_cfg_v2(void) { (void)spl_cranelift_new_aot_module_config_v2(0, 0, 0, 0, 0, 0, 0, 0, 0); }
static void call_isa_v2(void) { (void)spl_cranelift_aot_isa_feature_v2(0, 0, 0); }
static void call_opt_v2(void) { (void)spl_cranelift_aot_opt_level_v2(0); }

static const StubCase CASES[] = {
    {"rt_cranelift_new_module", call_new_module, (const void*)rt_cranelift_new_module},
    {"rt_cranelift_finalize_module", call_finalize, (const void*)rt_cranelift_finalize_module},
    {"rt_cranelift_free_module", call_free, (const void*)rt_cranelift_free_module},
    {"rt_cranelift_fconst", call_fconst, (const void*)rt_cranelift_fconst},
    {"rt_cranelift_bconst", call_bconst, (const void*)rt_cranelift_bconst},
    {"spl_cranelift_new_aot_module_config_v2", call_cfg_v2, (const void*)spl_cranelift_new_aot_module_config_v2},
    {"spl_cranelift_aot_isa_feature_v2", call_isa_v2, (const void*)spl_cranelift_aot_isa_feature_v2},
    {"spl_cranelift_aot_opt_level_v2", call_opt_v2, (const void*)spl_cranelift_aot_opt_level_v2},
};
#define N_CASES ((int)(sizeof(CASES) / sizeof(CASES[0])))

static int failures = 0;

static void check(int cond, const char* what, const char* sym) {
    printf("  %s %s: %s\n", cond ? "ok  " : "FAIL", sym, what);
    if (!cond) failures++;
}

int main(int argc, char** argv) {
    if (argc == 3 && strcmp(argv[1], "--child") == 0) {
        int idx = atoi(argv[2]);
        if (idx < 0 || idx >= N_CASES) return 2;
        CASES[idx].call();
        printf("CHILD-RETURNED\n"); /* reaching here is the failure */
        return 0;
    }
#if defined(_WIN32)
    /* abort() would otherwise pop a Windows Error Reporting dialog. */
    _set_abort_behavior(0, _WRITE_ABORT_MSG | _CALL_REPORTFAULT);
#endif
    printf("cranelift bridge stub smoke\n");
    for (int i = 0; i < N_CASES; i++) {
        const char* sym = CASES[i].name;
        check(CASES[i].addr != NULL, "symbol resolves at link time", sym);
        char cmd[1024];
        snprintf(cmd, sizeof(cmd), "\"\"%s\" --child %d 2>&1\"", argv[0], i);
#if !defined(_WIN32)
        snprintf(cmd, sizeof(cmd), "'%s' --child %d 2>&1", argv[0], i);
#endif
        FILE* p = SMOKE_POPEN(cmd, "r");
        if (!p) { check(0, "child spawned", sym); continue; }
        char out[4096];
        size_t n = fread(out, 1, sizeof(out) - 1, p);
        out[n] = '\0';
        int status = SMOKE_PCLOSE(p);
        char named[256];
        snprintf(named, sizeof(named), "`%s`", sym);
        check(status != 0, "call terminates the process (nonzero status)", sym);
        check(strstr(out, named) != NULL, "trap message names the exact symbol", sym);
        check(strstr(out, "NAMED TRAP") != NULL, "trap message says NAMED TRAP", sym);
        check(strstr(out, "CHILD-RETURNED") == NULL, "stub never returns a value", sym);
    }
    printf("%s (%d failures)\n", failures ? "FAIL" : "PASS", failures);
    return failures ? 1 : 0;
}
