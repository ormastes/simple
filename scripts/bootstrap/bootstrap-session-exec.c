/* Bootstrap syscall boundary: keep nested worker groups in the guard's session.
 * Build once before guarded execution; never compile in a worker launch path.
 *
 * POSIX: the session is a setsid() session; the Perl guard samples `ps`.
 * Windows: POSIX sessions/process groups do not exist and MSYS PIDs are not
 * Windows PIDs, so the session is a named Job Object owned by --supervise.
 * Every process created inside the job stays in it (no breakaway), which is
 * the Windows equivalent of "nested worker groups stay in the session". */
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#ifndef _CRT_SECURE_NO_WARNINGS
#define _CRT_SECURE_NO_WARNINGS
#endif
#include <windows.h>
#include <psapi.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

/* The MSYS shell is baked in at compile time, not passed by environment: the
 * bootstrap scrubs every child environment down to the three session-contract
 * variables, and the helper hash pinned by the guard then also pins the shell. */
#ifndef SIMPLE_BOOTSTRAP_SESSION_SHELL
#error "define SIMPLE_BOOTSTRAP_SESSION_SHELL as the absolute wide path of MSYS sh.exe"
#endif
static const wchar_t session_shell[] = SIMPLE_BOOTSTRAP_SESSION_SHELL;

static int reject(const char *reason) {
    fprintf(stderr, "bootstrap-session: %s\n", reason);
    return 125;
}

static int parse_u32(const wchar_t *text, unsigned long long max, unsigned long long *out) {
    unsigned long long value = 0;
    if (!text || !*text) return 0;
    for (const wchar_t *p = text; *p; ++p) {
        if (*p < L'0' || *p > L'9') return 0;
        value = value * 10 + (unsigned long long)(*p - L'0');
        if (value > max) return 0;
    }
    *out = value;
    return 1;
}

static int absolute_path(const wchar_t *p) {
    return p && (p[0] == L'/' ||
        (((p[0] | 0x20) >= L'a' && (p[0] | 0x20) <= L'z') && p[1] == L':' &&
         (p[2] == L'/' || p[2] == L'\\')));
}

static void job_name(wchar_t *name, size_t cap, unsigned long long id) {
    swprintf(name, cap, L"Local\\simple-bootstrap-session-%llu", id);
}

/* The contract is satisfied only when this process is a member of the job
 * named by SIMPLE_BOOTSTRAP_SESSION_ID. Absence of the job is a rejection. */
static int session_contract(unsigned long long *id_out) {
    const wchar_t *value = _wgetenv(L"SIMPLE_BOOTSTRAP_SESSION_ID");
    const wchar_t *helper = _wgetenv(L"SIMPLE_BOOTSTRAP_SESSION_EXEC");
    unsigned long long id;
    if (!value || !*value || !helper || !absolute_path(helper)) return reject("missing session contract");
    if (!parse_u32(value, 0x7fffffffULL, &id) || id == 0) return reject("invalid session ID");
    wchar_t name[96];
    job_name(name, 96, id);
    HANDLE job = OpenJobObjectW(JOB_OBJECT_QUERY, FALSE, name);
    if (!job) return reject("unexpected session ID");
    BOOL member = FALSE;
    BOOL ok = IsProcessInJob(GetCurrentProcess(), job, &member);
    CloseHandle(job);
    if (!ok || !member) return reject("unexpected session ID");
    if (id_out) *id_out = id;
    return 0;
}

typedef struct { wchar_t *text; size_t len, cap; } wbuf;

static int wbuf_put(wbuf *b, const wchar_t *s, size_t n) {
    if (b->len + n + 1 > b->cap) {
        size_t cap = b->cap ? b->cap : 256;
        while (b->len + n + 1 > cap) cap *= 2;
        wchar_t *grown = realloc(b->text, cap * sizeof(wchar_t));
        if (!grown) return 0;
        b->text = grown; b->cap = cap;
    }
    memcpy(b->text + b->len, s, n * sizeof(wchar_t));
    b->len += n;
    b->text[b->len] = 0;
    return 1;
}

/* Always quote (CommandLineToArgvW rules). An unquoted argument would be
 * glob-expanded by the MSYS runtime of the shell that receives it. */
static int wbuf_arg(wbuf *b, const wchar_t *arg) {
    if (b->len && !wbuf_put(b, L" ", 1)) return 0;
    if (!wbuf_put(b, L"\"", 1)) return 0;
    for (const wchar_t *p = arg;; ++p) {
        size_t slashes = 0;
        while (*p == L'\\') { ++p; ++slashes; }
        size_t emit = !*p ? slashes * 2 : *p == L'"' ? slashes * 2 + 1 : slashes;
        for (size_t i = 0; i < emit; ++i) if (!wbuf_put(b, L"\\", 1)) return 0;
        if (!*p) break;
        if (!wbuf_put(b, p, 1)) return 0;
    }
    return wbuf_put(b, L"\"", 1);
}

/* Commands may be shell scripts, so they are started through the MSYS shell,
 * exactly as a POSIX exec would resolve them: sh -c 'exec "$0" "$@"' ARGV. */
static wchar_t *shell_command_line(const wchar_t *shell, int argc, wchar_t **argv) {
    wbuf b = {0};
    if (!wbuf_arg(&b, shell) || !wbuf_put(&b, L" -c", 3) ||
        !wbuf_arg(&b, L"exec \"$0\" \"$@\"")) { free(b.text); return NULL; }
    for (int i = 0; i < argc; ++i)
        if (!wbuf_arg(&b, argv[i])) { free(b.text); return NULL; }
    return b.text;
}

static void inheritable_stdio(STARTUPINFOW *si) {
    memset(si, 0, sizeof(*si));
    si->cb = sizeof(*si);
    si->dwFlags = STARTF_USESTDHANDLES;
    HANDLE std[3] = { GetStdHandle(STD_INPUT_HANDLE), GetStdHandle(STD_OUTPUT_HANDLE),
                      GetStdHandle(STD_ERROR_HANDLE) };
    for (int i = 0; i < 3; ++i)
        if (std[i] && std[i] != INVALID_HANDLE_VALUE)
            SetHandleInformation(std[i], HANDLE_FLAG_INHERIT, HANDLE_FLAG_INHERIT);
    si->hStdInput = std[0]; si->hStdOutput = std[1]; si->hStdError = std[2];
}

/* `-- COMMAND`: the child inherits job membership; the job forbids breakaway. */
static int run_in_session(int argc, wchar_t **argv) {
    const wchar_t *shell = session_shell;
    if (!absolute_path(shell) || GetFileAttributesW(shell) == INVALID_FILE_ATTRIBUTES)
        return reject("missing session shell");
    wchar_t *line = shell_command_line(shell, argc, argv);
    if (!line) return reject("command line allocation failed");
    STARTUPINFOW si;
    PROCESS_INFORMATION pi;
    inheritable_stdio(&si);
    if (!CreateProcessW(shell, line, NULL, NULL, TRUE, CREATE_UNICODE_ENVIRONMENT,
                        NULL, NULL, &si, &pi)) {
        free(line);
        fprintf(stderr, "bootstrap-session: exec: CreateProcess error %lu\n", GetLastError());
        return 127;
    }
    free(line);
    CloseHandle(pi.hThread);
    DWORD code = 127;
    if (WaitForSingleObject(pi.hProcess, INFINITE) != WAIT_OBJECT_0 ||
        !GetExitCodeProcess(pi.hProcess, &code)) code = 127;
    CloseHandle(pi.hProcess);
    return (int)code;
}

/* ---- --supervise: job owner, RSS sampler and enforcer ------------------ */

typedef struct {
    const wchar_t *spec, *stats, *cap_mode;
    unsigned long long max_rss_kib, interval_ms, timeout_s, parent_pid, budget_ms;
    int inherit;
} options;

static char *read_file(const wchar_t *path, size_t *size) {
    FILE *f = _wfopen(path, L"rb");
    if (!f) return NULL;
    char *data = NULL;
    size_t len = 0, cap = 0, n;
    char chunk[4096];
    while ((n = fread(chunk, 1, sizeof chunk, f)) > 0) {
        if (len + n + 1 > cap) {
            cap = (len + n + 1) * 2;
            char *grown = realloc(data, cap);
            if (!grown) { free(data); fclose(f); return NULL; }
            data = grown;
        }
        memcpy(data + len, chunk, n);
        len += n;
    }
    fclose(f);
    if (!data) return NULL;
    data[len] = 0;
    *size = len;
    return data;
}

static wchar_t *widen(const char *s) {
    int n = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, s, -1, NULL, 0);
    if (n <= 0) return NULL;
    wchar_t *w = malloc((size_t)n * sizeof(wchar_t));
    if (w && MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, s, -1, w, n) != n) { free(w); w = NULL; }
    return w;
}

/* Working-set sum of every live job member, in KiB. A member that exits
 * between enumeration and query is skipped; any other failure fails closed. */
static int sample_job(HANDLE job, unsigned long long *kib, unsigned long *members) {
    static JOBOBJECT_BASIC_PROCESS_ID_LIST *list;
    static DWORD slots = 256;
    for (;;) {
        DWORD bytes = (DWORD)(sizeof(*list) + (slots - 1) * sizeof(ULONG_PTR));
        if (!list && !(list = malloc(bytes))) return 0;
        BOOL ok = QueryInformationJobObject(job, JobObjectBasicProcessIdList, list, bytes, NULL);
        if (ok && list->NumberOfProcessIdsInList >= list->NumberOfAssignedProcesses) break;
        if (!ok && GetLastError() != ERROR_MORE_DATA) return 0;
        if (slots >= 131072) return 0;
        slots *= 2;
        free(list); list = NULL;
    }
    unsigned long long total = 0;
    for (DWORD i = 0; i < list->NumberOfProcessIdsInList; ++i) {
        DWORD pid = (DWORD)list->ProcessIdList[i];
        HANDLE h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION | PROCESS_VM_READ, FALSE, pid);
        if (!h) {
            if (GetLastError() == ERROR_INVALID_PARAMETER) continue; /* already gone */
            return 0;
        }
        PROCESS_MEMORY_COUNTERS pmc;
        DWORD code = 0;
        if (!K32GetProcessMemoryInfo(h, &pmc, sizeof pmc)) {
            int gone = GetExitCodeProcess(h, &code) && code != STILL_ACTIVE;
            CloseHandle(h);
            if (gone) continue;
            return 0;
        }
        CloseHandle(h);
        total += pmc.WorkingSetSize;
    }
    *kib = total / 1024;
    *members = list->NumberOfProcessIdsInList;
    return 1;
}

static unsigned long long now_us(void) {
    static LARGE_INTEGER frequency;
    LARGE_INTEGER counter;
    if (!frequency.QuadPart) QueryPerformanceFrequency(&frequency);
    QueryPerformanceCounter(&counter);
    unsigned long long f = (unsigned long long)frequency.QuadPart, c = (unsigned long long)counter.QuadPart;
    return c / f * 1000000ULL + c % f * 1000000ULL / f;
}

static unsigned long active_processes(HANDLE job) {
    JOBOBJECT_BASIC_ACCOUNTING_INFORMATION info;
    if (!QueryInformationJobObject(job, JobObjectBasicAccountingInformation, &info, sizeof info, NULL))
        return (unsigned long)-1;
    return info.ActiveProcesses;
}

static int supervise(const options *o) {
    size_t spec_size = 0;
    char *spec = read_file(o->spec, &spec_size);
    if (!spec || spec_size == 0 || spec[spec_size - 1] != 0) return reject("unreadable workload spec");
    int count = 0;
    for (size_t i = 0; i < spec_size; ++i) if (!spec[i]) ++count;
    if (count < 2) return reject("workload spec needs session path and command");
    wchar_t **items = calloc((size_t)count, sizeof(wchar_t *));
    if (!items) return reject("allocation failed");
    for (size_t i = 0, k = 0; i < spec_size; i += strlen(spec + i) + 1, ++k)
        if (!(items[k] = widen(spec + i))) return reject("workload spec is not UTF-8");
    if (items[0][0] != L'/') return reject("session helper path must be POSIX-absolute");

    if (o->inherit && session_contract(NULL)) return reject("inherited session contract not satisfied");

    unsigned long long id = GetCurrentProcessId();
    wchar_t name[96], text[32];
    job_name(name, 96, id);
    HANDLE job = CreateJobObjectW(NULL, name);
    if (!job || GetLastError() == ERROR_ALREADY_EXISTS) return reject("cannot create session job");
    JOBOBJECT_EXTENDED_LIMIT_INFORMATION limits;
    memset(&limits, 0, sizeof limits);
    limits.BasicLimitInformation.LimitFlags =
        JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE | JOB_OBJECT_LIMIT_DIE_ON_UNHANDLED_EXCEPTION;
    if (!SetInformationJobObject(job, JobObjectExtendedLimitInformation, &limits, sizeof limits))
        return reject("cannot configure session job");
    HANDLE parent = NULL;
    if (o->parent_pid) {
        parent = OpenProcess(SYNCHRONIZE, FALSE, (DWORD)o->parent_pid);
        if (!parent) return reject("cannot watch supervising parent");
    }

    swprintf(text, 32, L"%llu", id);
    if (!SetEnvironmentVariableW(L"SIMPLE_BOOTSTRAP_SESSION_ID", text) ||
        !SetEnvironmentVariableW(L"SIMPLE_BOOTSTRAP_SESSION_EXEC", items[0]) ||
        !SetEnvironmentVariableW(L"SIMPLE_BOOTSTRAP_RSS_CAP_MODE", o->cap_mode))
        return reject("cannot publish session environment");
    if (GetFileAttributesW(session_shell) == INVALID_FILE_ATTRIBUTES) return reject("missing session shell");
    wchar_t *line = shell_command_line(session_shell, count - 1, items + 1);
    if (!line) return reject("command line allocation failed");
    STARTUPINFOW si;
    PROCESS_INFORMATION pi;
    inheritable_stdio(&si);
    /* Suspended until admitted: no workload instruction runs outside the job. */
    if (!CreateProcessW(session_shell, line, NULL, NULL, TRUE,
                        CREATE_SUSPENDED | CREATE_UNICODE_ENVIRONMENT, NULL, NULL, &si, &pi)) {
        fprintf(stderr, "bootstrap-session: exec: CreateProcess error %lu\n", GetLastError());
        return 127;
    }
    free(line);
    if (!AssignProcessToJobObject(job, pi.hProcess)) {
        TerminateProcess(pi.hProcess, 89);
        return reject("cannot admit workload into session job");
    }
    ResumeThread(pi.hThread);
    CloseHandle(pi.hThread);

    wchar_t stop[MAX_PATH + 8];
    swprintf(stop, MAX_PATH + 8, L"%ls.stop", o->stats);
    const char *status = "complete";
    int code = 0;
    /* Timing in microseconds (QPC); GetTickCount64 has ~15 ms granularity,
     * too coarse to report sampling overhead against a 100 ms cadence. */
    unsigned long long peak = 0, samples = 0, gap_max = 0, dur_max = 0, dur_total = 0, overruns = 0;
    unsigned long members_peak = 0;
    unsigned long long started = now_us(), previous = 0;
    for (;;) {
        unsigned long long at = now_us();
        if (previous && at - previous > gap_max) gap_max = at - previous;
        previous = at;
        unsigned long long kib = 0;
        unsigned long members = 0;
        if (!sample_job(job, &kib, &members)) { status = "rss-measurement-failed"; code = 89; break; }
        ++samples;
        unsigned long long duration = now_us() - at;
        dur_total += duration;
        if (duration > dur_max) dur_max = duration;
        if (duration > o->interval_ms * 1000) ++overruns;
        if (duration > o->budget_ms * 1000) { status = "rss-measurement-failed"; code = 89; break; }
        if (kib > peak) peak = kib;
        if (members > members_peak) members_peak = members;
        if (!wcscmp(o->cap_mode, L"enforce") && kib >= o->max_rss_kib) {
            status = "rss-cap-exceeded"; code = 88; break;
        }
        if (GetFileAttributesW(stop) != INVALID_FILE_ATTRIBUTES) { status = "interrupted"; code = 143; break; }
        if (parent && WaitForSingleObject(parent, 0) == WAIT_OBJECT_0) { status = "interrupted"; code = 129; break; }
        if (o->timeout_s && now_us() - started >= o->timeout_s * 1000000) {
            status = "timeout"; code = 124; break;
        }
        unsigned long long spent_ms = (now_us() - at) / 1000;
        DWORD wait = spent_ms >= o->interval_ms ? 0 : (DWORD)(o->interval_ms - spent_ms);
        if (WaitForSingleObject(pi.hProcess, wait) == WAIT_OBJECT_0) {
            DWORD exit_code = 0;
            if (!GetExitCodeProcess(pi.hProcess, &exit_code)) { status = "rss-measurement-failed"; code = 89; }
            else code = (int)exit_code;
            break;
        }
    }
    /* Quiesce: nothing of the workload survives the guard (POSIX quiesce()
     * likewise kills leftover members after a normal completion). */
    TerminateJobObject(job, strcmp(status, "complete") ? (UINT)code : 1u);
    int quiescent = 0;
    for (int i = 0; i < 250; ++i) {
        if (active_processes(job) == 0) { quiescent = 1; break; }
        Sleep(20);
    }
    WaitForSingleObject(pi.hProcess, 5000);
    JOBOBJECT_EXTENDED_LIMIT_INFORMATION peak_info;
    unsigned long long commit_kib = 0;
    if (QueryInformationJobObject(job, JobObjectExtendedLimitInformation, &peak_info, sizeof peak_info, NULL))
        commit_kib = (unsigned long long)peak_info.PeakJobMemoryUsed / 1024;
    if (!quiescent && code != 89) { status = "rss-containment-unverified"; code = 89; }

    wchar_t tmp[MAX_PATH + 8];
    swprintf(tmp, MAX_PATH + 8, L"%ls.tmp", o->stats);
    FILE *f = _wfopen(tmp, L"wb");
    if (!f) return reject("cannot write supervisor stats");
    fprintf(f, "status=%s\nexit_status=%d\nroot_pid=%lu\nsession_id=%llu\npeak_rss_kib=%llu\n"
               "samples=%llu\nsample_gap_max_ms=%llu\nsample_duration_max_ms=%llu\n"
               "sample_duration_max_us=%llu\nsample_duration_total_us=%llu\n"
               "sample_overruns=%llu\npeak_job_commit_kib=%llu\njob_members_peak=%lu\nquiescent=%d\n",
            status, code, pi.dwProcessId, id, peak, samples, gap_max / 1000, dur_max / 1000,
            dur_max, dur_total, overruns, commit_kib, members_peak, quiescent);
    if (fclose(f) || !MoveFileExW(tmp, o->stats, MOVEFILE_REPLACE_EXISTING))
        return reject("cannot publish supervisor stats");
    CloseHandle(pi.hProcess);
    CloseHandle(job);
    return code;
}

static int parse_supervise(int argc, wchar_t **argv, options *o) {
    memset(o, 0, sizeof *o);
    o->budget_ms = 1000;
    for (int i = 2; i < argc; ++i) {
        const wchar_t *a = argv[i], *v = i + 1 < argc ? argv[i + 1] : NULL;
        if (!wcscmp(a, L"--inherit")) { o->inherit = 1; continue; }
        if (!v) return 0;
        ++i;
        if (!wcscmp(a, L"--spec")) o->spec = v;
        else if (!wcscmp(a, L"--stats")) o->stats = v;
        else if (!wcscmp(a, L"--rss-cap-mode")) o->cap_mode = v;
        else if (!wcscmp(a, L"--max-rss-kib")) { if (!parse_u32(v, 5859375ULL, &o->max_rss_kib) || !o->max_rss_kib) return 0; }
        else if (!wcscmp(a, L"--interval-ms")) { if (!parse_u32(v, 100ULL, &o->interval_ms) || !o->interval_ms) return 0; }
        else if (!wcscmp(a, L"--observation-budget-ms")) { if (!parse_u32(v, 5000ULL, &o->budget_ms) || o->budget_ms < 1000) return 0; }
        else if (!wcscmp(a, L"--timeout-seconds")) { if (!parse_u32(v, 0x7fffffffULL, &o->timeout_s)) return 0; }
        else if (!wcscmp(a, L"--parent-winpid")) { if (!parse_u32(v, 0xffffffffULL, &o->parent_pid)) return 0; }
        else return 0;
    }
    return o->spec && o->stats && absolute_path(session_shell) && o->max_rss_kib && o->interval_ms &&
        o->cap_mode && (!wcscmp(o->cap_mode, L"enforce") || !wcscmp(o->cap_mode, L"monitor")) &&
        wcslen(o->stats) < MAX_PATH;
}

int wmain(int argc, wchar_t **argv) {
    if (argc >= 2 && !wcscmp(argv[1], L"--supervise")) {
        options o;
        if (!parse_supervise(argc, argv, &o)) return reject("invalid --supervise options");
        return supervise(&o);
    }
    /* getsid() has no Windows meaning; the guard never uses --sid here. */
    if (argc >= 2 && !wcscmp(argv[1], L"--sid"))
        return reject("--sid is POSIX-only; Windows sessions are job objects");
    int rc = session_contract(NULL);
    if (rc) return rc;
    if (argc == 2 && !wcscmp(argv[1], L"--check")) return 0;
    if (argc < 3 || wcscmp(argv[1], L"--")) return reject("expected -- COMMAND");
    return run_in_session(argc - 2, argv + 2);
}
#else
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int reject(const char *reason) {
    fprintf(stderr, "bootstrap-session: %s\n", reason);
    return 125;
}

int main(int argc, char **argv) {
    /* Batch observer for the parent guard. 0 means the PID disappeared; other
     * errors fail sampling. getsid(), not Darwin ps's session-address column,
     * is the authoritative POSIX session identity. */
    if (argc >= 3 && !strcmp(argv[1], "--sid")) {
        for (int i = 2; i < argc; ++i) {
            char *end;
            errno = 0;
            long pid = strtol(argv[i], &end, 10);
            if (errno || *end || !*argv[i] || pid < 0 || pid > INT_MAX)
                return reject("invalid observation PID");
            pid_t sid = getsid((pid_t)pid);
            if (sid < 0 && errno != ESRCH) return reject("getsid failed");
            printf("%ld %ld\n", pid, sid < 0 ? 0L : (long)sid);
        }
        return 0;
    }
    const char *value = getenv("SIMPLE_BOOTSTRAP_SESSION_ID");
    const char *helper = getenv("SIMPLE_BOOTSTRAP_SESSION_EXEC");
    if (!value || !*value || !helper || helper[0] != '/')
        return reject("missing session contract");
    for (const char *p = value; *p; ++p)
        if (*p < '0' || *p > '9') return reject("invalid session ID");
    char *end;
    errno = 0;
    long expected = strtol(value, &end, 10);
    if (errno || *end || expected <= 0 || expected > INT_MAX)
        return reject("invalid session ID");
    if (getsid(0) != (pid_t)expected)
        return reject("unexpected session ID");
    if (argc == 2 && !strcmp(argv[1], "--check")) return 0;
    if (argc < 3 || strcmp(argv[1], "--")) return reject("expected -- COMMAND");
    /* A runtime-spawned child may already lead its own group. In particular a
     * session leader cannot call setpgid(), but already has the required PGID. */
    if (getpgrp() != getpid() && setpgid(0, 0))
        return reject("setpgid failed");
    if (getsid(0) != (pid_t)expected || getpgrp() != getpid())
        return reject("worker identity mismatch");
    execvp(argv[2], argv + 2);
    perror("bootstrap-session: exec");
    return 127;
}
#endif
