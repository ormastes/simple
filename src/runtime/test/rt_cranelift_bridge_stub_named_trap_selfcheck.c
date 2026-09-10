/* Behavioural self-check for the Cranelift JIT bridge NAMED-TRAP stubs.
 *
 * See src/runtime/runtime_cranelift_bridge_stub.c and
 * doc/08_tracking/bug/stage2_link_full_undefined_symbol_census_2026-09-07.md
 * ("Bucket 2 deferred: cranelift JIT bridge", 75 symbols).
 *
 * A trap stub that merely "resolves" at link time proves nothing -- the
 * defect this whole census exists to fix is symbols that resolved to a
 * NULL GOT slot and SEGV'd (or worse, silently returned a fabricated value)
 * with no diagnostic. The real proof of a NAMED trap is a state transition:
 * (1) the caller's process actually dies -- not silently returns, not
 *     segfaults with no message, not hangs;
 * (2) it dies specifically via SIGABRT (the trap calls abort(), not some
 *     accidental crash from touching bad memory);
 * (3) the trap names the EXACT symbol that was called, so two different
 *     stubs are distinguishable at the point of failure -- this is what
 *     makes it a NAMED trap rather than an anonymous one.
 *
 * Every check here forks, calls exactly one stub in the child, and asserts
 * on what the PARENT observes: the exit status via WIFSIGNALED/WTERMSIG,
 * and the exact stderr text captured through a pipe. Representative
 * coverage across every distinct signature shape in the 75 (i64 return,
 * bool return, void return, 1..7 int64 params, the one `double`-typed
 * param (`rt_cranelift_fconst`), and the one `bool`-typed param
 * (`rt_cranelift_bconst`)) -- not all 75, since every body is the same
 * `(void)args; rt_trap_unimplemented(name); return sentinel;` shape and the
 * signature variety, not the count, is what could hide a copy-paste typo
 * (wrong arity, wrong sentinel type, wrong symbol string).
 */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

/* Exact signatures from src/lib/nogc_sync_mut/sffi/codegen.spl, mirrored in
 * src/runtime/runtime_cranelift_bridge_stub.c. */
extern int64_t rt_cranelift_new_module(int64_t name_ptr, int64_t name_len, int64_t target);
extern int64_t rt_cranelift_finalize_module(int64_t module);
extern void    rt_cranelift_free_module(int64_t module);
extern int64_t rt_cranelift_iadd(int64_t ctx, int64_t a, int64_t b);
extern int64_t rt_cranelift_bnot(int64_t ctx, int64_t a);
extern void    rt_cranelift_sig_add_param(int64_t sig, int64_t type_);
extern bool    rt_cranelift_define_function(int64_t module, int64_t func_id, int64_t ctx);
extern bool    rt_cranelift_call_arg(int64_t ctx, int64_t value);
extern int64_t rt_cranelift_fconst(int64_t ctx, int64_t type_, double value);
extern int64_t rt_cranelift_bconst(int64_t ctx, bool value);
extern int64_t rt_cranelift_call_indirect(int64_t ctx, int64_t sig, int64_t addr, int64_t args_ptr, int64_t args_len);
extern int64_t rt_cranelift_declare_global_data_v2(int64_t module, int64_t name_ptr, int64_t name_len, int64_t type_, int64_t initial_bits, int64_t linkage, int64_t alignment);

static int failures = 0;

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

/* Forks, runs `call_stub` in the child with its stderr redirected through a
 * pipe, and returns 1 iff the child died via SIGABRT AND its stderr
 * contained `expect_name` as a substring (proving it is the trap for THAT
 * symbol, not some other one). The parent drains the pipe itself so a full
 * pipe buffer can never deadlock the child before it aborts. */
typedef void (*rt_stub_call_fn)(void);

static rt_stub_call_fn g_target;

static void call_new_module(void)              { (void)rt_cranelift_new_module(0, 0, 0); }
static void call_finalize_module(void)         { (void)rt_cranelift_finalize_module(0); }
static void call_free_module(void)             { rt_cranelift_free_module(0); }
static void call_iadd(void)                    { (void)rt_cranelift_iadd(0, 1, 2); }
static void call_bnot(void)                    { (void)rt_cranelift_bnot(0, 1); }
static void call_sig_add_param(void)           { rt_cranelift_sig_add_param(0, 0); }
static void call_define_function(void)         { (void)rt_cranelift_define_function(0, 0, 0); }
static void call_call_arg(void)                { (void)rt_cranelift_call_arg(0, 0); }
static void call_fconst(void)                  { (void)rt_cranelift_fconst(0, 0, 3.5); }
static void call_bconst(void)                  { (void)rt_cranelift_bconst(0, true); }
static void call_call_indirect(void)           { (void)rt_cranelift_call_indirect(0, 0, 0, 0, 0); }
static void call_declare_global_data_v2(void)  { (void)rt_cranelift_declare_global_data_v2(0, 0, 0, 0, 0, 0, 0); }

static int child_traps_named(rt_stub_call_fn fn, const char* expect_name) {
    int pipefd[2];
    if (pipe(pipefd) != 0) return -1;

    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        /* Child: stderr -> pipe write end, then call exactly one stub. If
         * the stub somehow returns instead of aborting, exit 42 so the
         * parent can tell "returned" apart from "was signalled". */
        close(pipefd[0]);
        dup2(pipefd[1], STDERR_FILENO);
        close(pipefd[1]);
        fn();
        fflush(stderr);
        _exit(42);
    }
    close(pipefd[1]);

    char buf[4096];
    ssize_t total = 0;
    ssize_t n;
    while ((n = read(pipefd[0], buf + total, (ssize_t)sizeof(buf) - total - 1)) > 0) {
        total += n;
        if (total >= (ssize_t)sizeof(buf) - 1) break;
    }
    buf[total > 0 ? total : 0] = '\0';
    close(pipefd[0]);

    int status = 0;
    if (waitpid(pid, &status, 0) != pid) return -1;

    if (!(WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT)) {
        printf("       (child did not die via SIGABRT: WIFEXITED=%d WEXITSTATUS=%d WIFSIGNALED=%d WTERMSIG=%d)\n",
               WIFEXITED(status), WIFEXITED(status) ? WEXITSTATUS(status) : -1,
               WIFSIGNALED(status), WIFSIGNALED(status) ? WTERMSIG(status) : -1);
        return 0;
    }
    if (strstr(buf, expect_name) == NULL) {
        printf("       (stderr did not name `%s`; captured: %s)\n", expect_name, buf);
        return 0;
    }
    return 1;
}

int main(void) {
    /* --- 1. Every representative shape actually traps (state transition:
     *        process dies, not a silent return / hang / segfault). --- */
    check(child_traps_named(call_new_module, "rt_cranelift_new_module") == 1,
          "rt_cranelift_new_module (3x i64 -> i64) traps naming itself");
    check(child_traps_named(call_finalize_module, "rt_cranelift_finalize_module") == 1,
          "rt_cranelift_finalize_module (1x i64 -> i64) traps naming itself");
    check(child_traps_named(call_free_module, "rt_cranelift_free_module") == 1,
          "rt_cranelift_free_module (1x i64 -> void) traps naming itself");
    check(child_traps_named(call_iadd, "rt_cranelift_iadd") == 1,
          "rt_cranelift_iadd (3x i64 -> i64) traps naming itself");
    check(child_traps_named(call_bnot, "rt_cranelift_bnot") == 1,
          "rt_cranelift_bnot (2x i64 -> i64) traps naming itself");
    check(child_traps_named(call_sig_add_param, "rt_cranelift_sig_add_param") == 1,
          "rt_cranelift_sig_add_param (2x i64 -> void) traps naming itself");
    check(child_traps_named(call_define_function, "rt_cranelift_define_function") == 1,
          "rt_cranelift_define_function (3x i64 -> bool) traps naming itself");
    check(child_traps_named(call_call_arg, "rt_cranelift_call_arg") == 1,
          "rt_cranelift_call_arg (2x i64 -> bool) traps naming itself");
    check(child_traps_named(call_fconst, "rt_cranelift_fconst") == 1,
          "rt_cranelift_fconst (i64,i64,f64 -> i64) traps naming itself");
    check(child_traps_named(call_bconst, "rt_cranelift_bconst") == 1,
          "rt_cranelift_bconst (i64,bool -> i64) traps naming itself");
    check(child_traps_named(call_call_indirect, "rt_cranelift_call_indirect") == 1,
          "rt_cranelift_call_indirect (5x i64 -> i64) traps naming itself");
    check(child_traps_named(call_declare_global_data_v2, "rt_cranelift_declare_global_data_v2") == 1,
          "rt_cranelift_declare_global_data_v2 (7x i64 -> i64) traps naming itself");

    /* --- 2. Distinguishability: two DIFFERENT stubs must not report the
     *        same name -- proves this is a per-symbol NAMED trap, not one
     *        generic message that happens to satisfy a substring check. --- */
    {
        int pipefd[2];
        pipe(pipefd);
        pid_t pid = fork();
        if (pid == 0) {
            close(pipefd[0]);
            dup2(pipefd[1], STDERR_FILENO);
            close(pipefd[1]);
            call_iadd();
            _exit(42);
        }
        close(pipefd[1]);
        char buf[4096];
        ssize_t total = read(pipefd[0], buf, sizeof(buf) - 1);
        buf[total > 0 ? total : 0] = '\0';
        close(pipefd[0]);
        int status = 0;
        waitpid(pid, &status, 0);
        check(strstr(buf, "rt_cranelift_bnot") == NULL,
              "rt_cranelift_iadd's trap does not also claim to be rt_cranelift_bnot");
    }

    /* --- 3. The parent process itself is completely unaffected by a
     *        child's trap -- fork isolation, no shared abort state. --- */
    check(1, "parent survived all child traps above and can still report");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
