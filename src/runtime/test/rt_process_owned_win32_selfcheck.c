/* Win32 bounded-child capsule selfcheck.
 *
 * Covers the `#elif defined(_WIN32)` branch of src/runtime/runtime_process_owned.c,
 * added 2026-09-13. Before that branch existed, EVERY bounded spawn on Windows
 * fell through to the ENOTSUP stub and returned rc=-1, which is what broke the
 * ctx_tools / ctx_batch_scale / token_stats specs and check-mcp-native-smoke.
 *
 * The sibling runtime_process_owned_selfcheck.c is POSIX-only (pthread.h,
 * unistd.h, signal semantics) and is skipped on Windows, so this is the
 * Windows-side twin rather than a duplicate.
 *
 * Build and run (this file is compiled with the SplArray ABI wrappers removed,
 * so no Simple runtime needs to be linked):
 *
 *   clang -DRT_PROCESS_OWNED_CORE_ONLY -I src/runtime -I src/runtime/include \
 *       -o build/rt_process_owned_win32_selfcheck.exe \
 *       src/runtime/test/rt_process_owned_win32_selfcheck.c \
 *       src/runtime/runtime_process_owned.c
 *   ./build/rt_process_owned_win32_selfcheck.exe
 *
 * Verdict is the last line of stdout: "PASS: 0 failure(s)" (exit 0) or
 * "FAIL: <n> failure(s)" (exit 1). On a non-Windows host the whole body
 * compiles away and the program reports that it checked nothing, so a green
 * exit there is never mistaken for Windows evidence.
 */

#if defined(_WIN32)

#include <windows.h>

#include "runtime.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int failures = 0;
static int checks = 0;

static void check(const char* name, int cond, const char* detail) {
    checks++;
    if (cond) {
        printf("  ok   %s\n", name);
    } else {
        printf("  FAIL %s (%s)\n", name, detail);
        failures++;
    }
}

/* --- concurrency: the handle-list bound, not a bare bInheritHandles ------- */
#define CONC_N 6
static int conc_ok[CONC_N];
static DWORD conc_ms[CONC_N];

static DWORD WINAPI conc_worker(LPVOID arg) {
    int i = (int)(intptr_t)arg;
    char out[8192];
    char err[8192];
    RtOwnedProcessReceipt r;
    const char* argv[] = {"cmd.exe", "/c", "echo conc", NULL};
    DWORD t0 = GetTickCount();
    (void)rt_process_run_owned_bounded("cmd.exe", argv, 20000, sizeof(out) - 1,
                                       out, sizeof(out), err, sizeof(err), &r);
    conc_ms[i] = GetTickCount() - t0;
    conc_ok[i] = (r.runtime_error == 0 && r.exit_code == 0 && r.timed_out == 0 &&
                  strstr(out, "conc") != NULL) ? 1 : 0;
    return 0;
}

static int zero_child_mode(int argc, char** argv) {
    if (argc==2 && strcmp(argv[1],"--zero-sleep-child")==0) {
        Sleep(600);
        return 0;
    }
    if (argc==3 && strcmp(argv[1],"--zero-pipe-child")==0) {
        if (strcmp(argv[2],"idle")==0) Sleep(5000);
        else {
            char bytes[4096]; memset(bytes,'w',sizeof(bytes));
            ULONGLONG until=GetTickCount64()+5000;
            while (GetTickCount64()<until) {
                DWORD wrote=0;
                if (!WriteFile(GetStdHandle(STD_OUTPUT_HANDLE),bytes,sizeof(bytes),&wrote,NULL)) break;
            }
        }
        return 0;
    }
    if (argc==3 && strcmp(argv[1],"--zero-pipe-parent")==0) {
        char self[MAX_PATH], command[2*MAX_PATH];
        if (!GetModuleFileNameA(NULL,self,sizeof(self))) return 81;
        snprintf(command,sizeof(command),"\"%s\" --zero-pipe-child %s",self,argv[2]);
        STARTUPINFOA startup; PROCESS_INFORMATION child;
        memset(&startup,0,sizeof(startup)); memset(&child,0,sizeof(child));
        startup.cb=sizeof(startup); startup.dwFlags=STARTF_USESTDHANDLES;
        startup.hStdInput=GetStdHandle(STD_INPUT_HANDLE);
        startup.hStdOutput=GetStdHandle(STD_OUTPUT_HANDLE);
        startup.hStdError=GetStdHandle(STD_ERROR_HANDLE);
        if (!CreateProcessA(self,command,NULL,NULL,TRUE,CREATE_NO_WINDOW,NULL,NULL,&startup,&child)) return 82;
        CloseHandle(child.hThread); CloseHandle(child.hProcess);
        return 0;
    }
    return -1;
}

static void zero_deadline_checks(void) {
    char self[MAX_PATH], out[4096], err[4096];
    RtOwnedProcessReceipt receipt;
    check("locate test executable",GetModuleFileNameA(NULL,self,sizeof(self))>0,"module path unavailable");
    const char* sleeper[]={self,"--zero-sleep-child",NULL};
    DWORD started=GetTickCount();
    bool ok=rt_process_run_owned_bounded(self,sleeper,0,sizeof(out)-1,
        out,sizeof(out),err,sizeof(err),&receipt);
    DWORD elapsed=GetTickCount()-started;
    check("zero work budget completes naturally",ok && receipt.reaped && receipt.exit_code==0 &&
        !receipt.timed_out && !receipt.kill_sent,"zero expired or failed");
    check("zero survives positive deadline boundary",elapsed>=500 && elapsed<3000,"unexpected lifetime");
    (void)rt_process_run_owned_bounded(self,sleeper,100,sizeof(out)-1,
        out,sizeof(out),err,sizeof(err),&receipt);
    check("positive deadline still expires",receipt.timed_out && receipt.kill_sent && receipt.reaped,
        "positive work limit missing");
    const char* modes[]={"idle","active"};
    for(int index=0;index<2;index++) {
        const char* parent[]={self,"--zero-pipe-parent",modes[index],NULL};
        started=GetTickCount();
        ok=rt_process_run_owned_bounded(self,parent,0,sizeof(out)-1,
            out,sizeof(out),err,sizeof(err),&receipt);
        elapsed=GetTickCount()-started;
        printf("  info zero inherited %s elapsed_ms=%lu\n",modes[index],(unsigned long)elapsed);
        check(modes[index],ok && receipt.exit_code==0 && receipt.reaped && !receipt.timed_out &&
            receipt.kill_sent && receipt.stdout_truncated && elapsed<3000,
            "inherited pipe cleanup lost its bound");
    }
    (void)rt_process_run_owned_bounded(self,sleeper,-1,sizeof(out)-1,
        out,sizeof(out),err,sizeof(err),&receipt);
    check("negative deadline rejected",receipt.runtime_error==EINVAL,"negative accepted");
}

int main(int argc, char** argv) {
    int child_result=zero_child_mode(argc,argv);
    if(child_result>=0) return child_result;
    if(argc==2 && strcmp(argv[1],"--zero-deadline-only")==0) {
        zero_deadline_checks();
        printf("%s: %d failure(s), %d zero-deadline checks\n",failures ? "FAIL" : "PASS",failures,checks);
        return failures ? 1 : 0;
    }
    char out[65536];
    char err[65536];
    RtOwnedProcessReceipt r;
    RtOwnedProcessObservationV1 obs;

    /* 1. a child that exits 0 runs, is reaped, and its stdout is captured. */
    {
        const char* argv[] = {"cmd.exe", "/c", "echo hi", NULL};
        bool ok = rt_process_run_owned_bounded("cmd.exe", argv, 10000, sizeof(out) - 1,
                                               out, sizeof(out), err, sizeof(err), &r);
        check("spawn succeeds", ok && r.runtime_error == 0, "runtime_error set");
        check("exit_code 0", r.exit_code == 0, "nonzero exit");
        check("stdout captured", strstr(out, "hi") != NULL, "empty stdout");
        check("reaped", r.reaped == 1, "not reaped");
    }

    /* 2. a non-zero exit code survives, rather than collapsing to -1. */
    {
        const char* argv[] = {"cmd.exe", "/c", "exit 3", NULL};
        (void)rt_process_run_owned_bounded("cmd.exe", argv, 10000, sizeof(out) - 1,
                                           out, sizeof(out), err, sizeof(err), &r);
        check("exit_code 3", r.exit_code == 3, "exit code lost");
    }

    /* 3. stderr is a separate stream, not folded into stdout. */
    {
        const char* argv[] = {"cmd.exe", "/c", "echo oops 1>&2", NULL};
        (void)rt_process_run_owned_bounded("cmd.exe", argv, 10000, sizeof(out) - 1,
                                           out, sizeof(out), err, sizeof(err), &r);
        check("stderr captured", strstr(err, "oops") != NULL, "empty stderr");
        check("stdout stays empty", strstr(out, "oops") == NULL, "streams merged");
    }

    /* 4. the deadline is real: a ~30s child bounded to 700ms must die. */
    {
        const char* argv[] = {"cmd.exe", "/c", "ping -n 30 127.0.0.1 > NUL", NULL};
        DWORD t0 = GetTickCount();
        (void)rt_process_run_owned_bounded("cmd.exe", argv, 700, sizeof(out) - 1,
                                           out, sizeof(out), err, sizeof(err), &r);
        DWORD dt = GetTickCount() - t0;
        printf("  info deadline elapsed_ms=%lu\n", (unsigned long)dt);
        check("timed_out recorded", r.timed_out == 1, "deadline not enforced");
        check("kill recorded", r.kill_sent == 1, "no kill recorded");
        check("returned promptly", dt < 5000, "rode past the deadline");
    }

    /* 5. the output cap truncates and reports seen separately from kept. */
    {
        const char* argv[] = {
            "cmd.exe", "/c",
            "for /L %i in (1,1,2000) do @echo aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", NULL};
        /* The destination is deliberately larger than the policy cap. This
         * exposes direct-ABI implementations that use storage capacity as the
         * retained-output limit. */
        char capped[4097];
        (void)rt_process_run_owned_bounded("cmd.exe", argv, 30000, 1000,
                                           capped, sizeof(capped), err, sizeof(err), &r);
        check("truncation flagged", r.stdout_truncated == 1, "no truncation recorded");
        check("policy cap respected", r.stdout_bytes_kept == 1000,
              "max_output_bytes ignored");
        check("seen exceeds kept", r.stdout_bytes_seen > r.stdout_bytes_kept,
              "seen not counted past the cap");
    }

    /* 6. the observed variant fills real job accounting, not zeros. */
    {
        const char* argv[] = {"cmd.exe", "/c", "echo obs", NULL};
        (void)rt_process_run_owned_observed_bounded("cmd.exe", argv, 10000, sizeof(out) - 1,
                                                    out, sizeof(out), err, sizeof(err),
                                                    &r, &obs);
        check("observation ok", obs.runtime_error == 0, "observation errored");
        check("evidence flags set", obs.evidence_flags != 0, "no evidence recorded");
        check("pid accounting", obs.pids_peak >= 1, "no pids counted");
    }

    /* 7. Zero is unlimited useful work; only negative timeout is invalid. */
    {
        const char* argv[] = {"cmd.exe", "/c", "echo x", NULL};
        bool ok = rt_process_run_owned_bounded("cmd.exe", argv, 0, sizeof(out) - 1,
                                               out, sizeof(out), err, sizeof(err), &r);
        check("zero timeout accepted", ok && r.exit_code==0 && !r.timed_out,
              "zero workload limit was rejected");
        ok = rt_process_run_owned_bounded("cmd.exe", argv, -1, sizeof(out) - 1,
                                           out, sizeof(out), err, sizeof(err), &r);
        check("EINVAL on negative timeout", !ok && r.runtime_error == EINVAL,
              "negative workload limit accepted");
    }

    /* 8. a missing program fails loudly rather than reporting a silent success. */
    {
        const char* argv[] = {"./no_such_program_xyz", NULL};
        bool ok = rt_process_run_owned_bounded("./no_such_program_xyz", argv, 5000,
                                               sizeof(out) - 1, out, sizeof(out),
                                               err, sizeof(err), &r);
        check("missing program reported", !ok && r.runtime_error != 0, "silent success");
    }

    /* 9. argv quoting is the CommandLineToArgvW inverse: spaces do not split. */
    {
        const char* argv[] = {"cmd.exe", "/c", "echo", "a b c", NULL};
        (void)rt_process_run_owned_bounded("cmd.exe", argv, 10000, sizeof(out) - 1,
                                           out, sizeof(out), err, sizeof(err), &r);
        check("spaced argument intact", strstr(out, "a b c") != NULL, "argv split on space");
    }

    /* 10. concurrent spawns do not starve each other of EOF. A bare
     *     bInheritHandles=TRUE leaks every child's pipe write end into every
     *     other child, and the symptom is that all of them ride their deadline. */
    {
        HANDLE th[CONC_N];
        int bad = 0;
        DWORD worst = 0;
        for (int i = 0; i < CONC_N; i++) {
            th[i] = CreateThread(NULL, 0, conc_worker, (LPVOID)(intptr_t)i, 0, NULL);
        }
        WaitForMultipleObjects(CONC_N, th, TRUE, INFINITE);
        for (int i = 0; i < CONC_N; i++) {
            if (!conc_ok[i]) bad++;
            if (conc_ms[i] > worst) worst = conc_ms[i];
            CloseHandle(th[i]);
        }
        printf("  info concurrent worst_ms=%lu\n", (unsigned long)worst);
        check("all concurrent spawns succeeded", bad == 0, "a concurrent spawn failed");
        check("no EOF starvation", worst < 5000, "concurrent spawns rode their deadline");
    }

    if (checks == 0) {
        printf("ERROR: nothing was checked\n");
        return 2;
    }
    printf("%s: %d failure(s) over %d check(s)\n",
           failures ? "FAIL" : "PASS", failures, checks);
    return failures ? 1 : 0;
}

#else

#include <stdio.h>

int main(void) {
    /* Not a pass: this selfcheck makes claims only about the Win32 branch. */
    printf("SKIP: rt_process_owned_win32_selfcheck requires a Windows host\n");
    return 0;
}

#endif
