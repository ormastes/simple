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

/* Crash classification parity with POSIX 128+signal. A native process that
 * dies from an exception exits with its NTSTATUS; mapping it keeps e.g. an
 * access violation at 139 instead of its truncated low byte (0x05 -> "exit 5"). */
static int ntstatus_to_posix(DWORD status) {
    switch (status) {
    case 0xC0000005: case 0xC0000006: case 0xC00000FD: return 128 + 11; /* SIGSEGV */
    case 0xC000001D: case 0xC0000096: return 128 + 4;                   /* SIGILL */
    case 0xC000008C: case 0xC000008D: case 0xC000008E: case 0xC000008F:
    case 0xC0000090: case 0xC0000091: case 0xC0000092: case 0xC0000093:
    case 0xC0000094: case 0xC0000095: return 128 + 8;                   /* SIGFPE */
    case 0x80000002: return 128 + 7;                                    /* SIGBUS */
    case 0x80000003: case 0x80000004: return 128 + 5;                   /* SIGTRAP */
    case 0xC000013A: return 128 + 2;                                    /* SIGINT */
    default: return 128 + 6; /* SIGABRT: fastfail 0xC0000409 and any other fatal status */
    }
}

/* Map a root exit code to a POSIX-style status. `abnormal` is the NTSTATUS of
 * the last job member that died from an exception (0 if none). The root is an
 * MSYS shell stub: it reports a signal death as sig<<8 (0xB00 for an access
 * violation) and collapses exceptions it does not know to 0x7f. */
static int posix_exit_status(DWORD raw, DWORD abnormal) {
    if (raw >= 0x80000000) return ntstatus_to_posix(raw);
    if (raw == 0x7f && abnormal) return ntstatus_to_posix(abnormal);
    /* MSYS also truncates some statuses to their low byte (0x80000003 -> 3). */
    if (abnormal && raw && raw == (abnormal & 0xff)) return ntstatus_to_posix(abnormal);
    if (raw <= 0xff) return (int)raw;
    DWORD sig = (raw >> 8) & 0x7f;
    return (raw & 0xff) == 0 && sig >= 1 && sig < 64 ? 128 + (int)sig : 128 + 6;
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
    return posix_exit_status(code, 0);
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

/* NTSTATUS of the last job member that died from an exception. The kernel
 * posts JOB_OBJECT_MSG_ABNORMAL_EXIT_PROCESS; the exit code is read at once,
 * while the member's MSYS parent still holds its process handle. */
static volatile LONG abnormal_status;

static DWORD WINAPI abnormal_exit_watch(LPVOID port) {
    DWORD message;
    ULONG_PTR key;
    LPOVERLAPPED data;
    while (GetQueuedCompletionStatus((HANDLE)port, &message, &key, &data, INFINITE)) {
        /* Not every fatal status is on the kernel's "abnormal" list (e.g. the
         * fastfail 0xC0000409 arrives as a plain exit), so inspect both. */
        int abnormal = message == JOB_OBJECT_MSG_ABNORMAL_EXIT_PROCESS;
        if (!abnormal && message != JOB_OBJECT_MSG_EXIT_PROCESS) continue;
        DWORD code = 0;
        HANDLE h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, (DWORD)(ULONG_PTR)data);
        if (h) {
            if (!GetExitCodeProcess(h, &code)) code = 0;
            CloseHandle(h);
        }
        if (code >= 0x80000000) InterlockedExchange(&abnormal_status, (LONG)code);
        else if (abnormal) InterlockedExchange(&abnormal_status, (LONG)0xC0000000); /* unreadable */
    }
    return 0;
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
    JOBOBJECT_ASSOCIATE_COMPLETION_PORT association;
    association.CompletionKey = job;
    association.CompletionPort = CreateIoCompletionPort(INVALID_HANDLE_VALUE, NULL, 0, 1);
    if (!association.CompletionPort ||
        !SetInformationJobObject(job, JobObjectAssociateCompletionPortInformation, &association, sizeof association) ||
        !CreateThread(NULL, 0, abnormal_exit_watch, association.CompletionPort, 0, NULL))
        return reject("cannot watch session job exits");
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
    DWORD root_raw = 0;
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
            if (!GetExitCodeProcess(pi.hProcess, &root_raw)) { status = "rss-measurement-failed"; code = 89; }
            else {
                /* 0x7f may be a collapsed exception: let the exit watcher land. */
                for (int i = 0; root_raw == 0x7f && !abnormal_status && i < 20; ++i) Sleep(10);
                code = posix_exit_status(root_raw, (DWORD)abnormal_status);
            }
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
               "sample_overruns=%llu\npeak_job_commit_kib=%llu\njob_members_peak=%lu\nquiescent=%d\n"
               "root_exit_raw=0x%lx\nabnormal_exit_ntstatus=0x%lx\n",
            status, code, pi.dwProcessId, id, peak, samples, gap_max / 1000, dur_max / 1000,
            dur_max, dur_total, overruns, commit_kib, members_peak, quiescent,
            root_raw, (unsigned long)abnormal_status);
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
        else if (!wcscmp(a, L"--max-rss-kib")) {
            /* Policy (the job-scaled ceiling) belongs to the watchdog that
               launches this helper. The mechanism only refuses a cap that
               could never fire: one at or above host physical memory, so
               the largest accepted value is one KiB below it. */
            MEMORYSTATUSEX mem;
            mem.dwLength = sizeof mem;
            if (!GlobalMemoryStatusEx(&mem)) { reject("cannot read host physical memory"); return 0; }
            if (mem.ullTotalPhys / 1024 < 2 ||
                !parse_u32(v, mem.ullTotalPhys / 1024 - 1, &o->max_rss_kib) || !o->max_rss_kib) {
                fprintf(stderr, "bootstrap-session: --max-rss-kib must be at least 1 and below host physical memory (%llu KiB)\n",
                        (unsigned long long)(mem.ullTotalPhys / 1024));
                return 0;
            }
        }
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
#ifndef __FreeBSD__
#define _POSIX_C_SOURCE 200809L
#endif
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

#ifdef __FreeBSD__
#include <sys/types.h>
#include <sys/sysctl.h>
#include <sys/user.h>
#include <sys/proc.h>
#include <sys/procctl.h>
#include <sys/wait.h>
#include <poll.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>
#include <stdint.h>

/* Ownership mechanism only: RSS limits, workload deadlines, TERM grace and
 * receipts remain in Perl. This owner never executes workload code itself. */
#define REAP_ROWS 16384
#define REAP_DEPTH 64
#define REAP_FRAME (REAP_ROWS * 160 + 512)
struct owned_row {
    struct kinfo_proc info;
    pid_t reaper;
    unsigned depth;
    int nested;
};
static volatile sig_atomic_t reap_stop;
static pid_t reap_payload;
static int reap_status_raw = -1;
static double reap_deadline;
static const char *reap_failure = "none";
static pid_t reap_failure_pid;
static int reap_failure_errno;

/* Remember a fixed diagnostic stage without process names or argv. */
static void reap_failed(const char *reason, pid_t pid, int error) {
    reap_failure = reason;
    reap_failure_pid = pid;
    reap_failure_errno = error;
}

static double reap_clock(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) return -1;
    return (double)t.tv_sec + t.tv_nsec / 1000000000.0;
}
static void reap_interrupted(int sig) { reap_stop = sig; }
static void reap_report(int output, const char *phase, const char *reason,
    pid_t pid, int error, unsigned attempts, int quiet) {
    char line[256];
    int n = snprintf(line, sizeof(line), "ERROR 1 %d %s %s %d %d %u %d %d %d\n",
        getpid(), phase, reason, pid, error, attempts, (int)reap_stop, quiet, reap_status_raw);
    /* The private output pipe is O_NONBLOCK and 256 <= PIPE_BUF: one atomic,
     * best-effort write, never a retry or a wait. A full/broken pipe may lose
     * diagnostics, but must not stall cleanup. Inherited stderr may be full. */
    if (n > 0 && n < (int)sizeof(line)) (void)write(output, line, (size_t)n);
}
static int reap_within(void) {
    double now = reap_clock();
    return now >= 0 && now < reap_deadline && !reap_stop;
}
static int reap_metadata(pid_t pid, struct kinfo_proc *p) {
    int mib[] = {CTL_KERN, KERN_PROC, KERN_PROC_PID, pid};
    size_t size = sizeof(*p);
    memset(p, 0, sizeof(*p));
    if (sysctl(mib, 4, p, &size, NULL, 0)) return errno == ESRCH ? 0 : -1;
    if (!size) return 0;
    if (size != sizeof(*p) || p->ki_structsize != sizeof(*p) || p->ki_pid != pid) {
        errno = EPROTO;
        return -1;
    }
    return 1;
}
static int reap_same(const struct kinfo_proc *a, const struct kinfo_proc *b) {
    return a->ki_pid == b->ki_pid && a->ki_start.tv_sec == b->ki_start.tv_sec &&
        a->ki_start.tv_usec == b->ki_start.tv_usec;
}
static int reap_owned(pid_t pid) {
    struct procctl_reaper_status s = {0};
    if (procctl(P_PID, pid, PROC_REAP_STATUS, &s)) {
        reap_failed("owner-status-query", pid, errno);
        return 0;
    }
    if (!(s.rs_flags & REAPER_STATUS_OWNED) || (s.rs_flags & REAPER_STATUS_REALINIT) ||
        s.rs_reaper != pid) {
        reap_failed("owner-status-changed", pid, 0);
        return 0;
    }
    return 1;
}
/* Reserve one extra entry: a full list is ambiguous, never a complete sample. */
static struct procctl_reaper_pidinfo *reap_list(pid_t pid, unsigned *count) {
    if (!reap_within()) { reap_failed("list-budget-or-signal", pid, 0); return NULL; }
    if (!reap_owned(pid)) return NULL;
    struct procctl_reaper_pidinfo *rows = calloc(REAP_ROWS + 1, sizeof(*rows));
    if (!rows) { reap_failed("list-allocation", pid, errno); return NULL; }
    struct procctl_reaper_pids request = {0};
    request.rp_count = REAP_ROWS + 1;
    request.rp_pids = rows;
    if (procctl(P_PID, pid, PROC_REAP_GETPIDS, &request)) {
        reap_failed("list-query", pid, errno); free(rows); return NULL;
    }
    *count = 0;
    while (*count <= REAP_ROWS && (rows[*count].pi_flags & REAPER_PIDINFO_VALID))
        ++*count;
    if (*count > REAP_ROWS) { reap_failed("list-saturated", pid, 0); free(rows); return NULL; }
    if (!reap_owned(pid)) { free(rows); return NULL; }
    if (!reap_within()) { reap_failed("list-budget-or-signal", pid, 0); free(rows); return NULL; }
    return rows;
}
static void reap_wait(void) {
    int status;
    pid_t pid;
    double until = reap_clock() + 0.002;
    /* A fork/exit stream must not starve commands or cleanup deadlines. Partial
     * draining is not quiescence: cleanup separately checks kernel ownership. */
    for (unsigned i = 0; i < 256 && reap_clock() < until; ++i) {
        pid = waitpid(-1, &status, WNOHANG);
        if (pid <= 0) break;
        if (pid == reap_payload) reap_status_raw = status;
    }
}
static int reap_signal_all(int signal) {
    struct procctl_reaper_kill k = {0};
    k.rk_sig = signal;
    int rc = procctl(P_PID, getpid(), PROC_REAP_KILL, &k);
    /* ESRCH with no failed PID means an empty hierarchy, not a signal failure. */
    return (rc == 0 || (errno == ESRCH && k.rk_killed == 0)) && k.rk_fpid == -1;
}
static int reap_cleanup(void) {
    double now = reap_clock();
    if (now < 0) return 0;
    double until = now + 2.0;
    if (!reap_owned(getpid())) return 0;
    do {
        int stopped = reap_signal_all(SIGSTOP);
        int killed = reap_signal_all(SIGKILL);
        if (!stopped || !killed) return 0;
        reap_wait();
        struct procctl_reaper_status s = {0};
        if (procctl(P_PID, getpid(), PROC_REAP_STATUS, &s) ||
            !(s.rs_flags & REAPER_STATUS_OWNED)) return 0;
        if (s.rs_descendants == 0 && reap_status_raw >= 0) return 1;
        struct timespec delay = {0, 10000000};
        nanosleep(&delay, NULL);
        now = reap_clock();
    } while (now >= 0 && now < until);
    return 0;
}
static int reap_write(int fd, const char *data, size_t size, double until) {
    while (size) {
        double now = reap_clock();
        if (now < 0) return 0;
        double left = until - now;
        if (left <= 0) return 0;
        struct pollfd p = {fd, POLLOUT, 0};
        int rc = poll(&p, 1, (int)(left * 1000) + 1);
        if (rc < 0 && errno == EINTR) continue;
        if (rc <= 0 || !(p.revents & POLLOUT)) return 0;
        ssize_t n = write(fd, data, size);
        if (n < 0 && (errno == EINTR || errno == EAGAIN)) continue;
        if (n <= 0) return 0;
        data += n; size -= (size_t)n;
    }
    return 1;
}
static int reap_sample_once(int output) {
    /* Bounded allocation; rows carry native birth identities, not ps lstart. */
    struct owned_row *rows = calloc(REAP_ROWS + 1, sizeof(*rows));
    /* Two bounded lists per reaper, not two parent scans per nested child. */
    pid_t *membership = calloc(REAP_ROWS * 2, sizeof(*membership));
    unsigned *generation = calloc(REAP_ROWS * 2, sizeof(*generation));
    char *frame = malloc(REAP_FRAME);
    int ok = 0;
    unsigned used = 1;
    if (!rows || !frame || !membership || !generation) {
        reap_failed("sample-allocation", getpid(), ENOMEM); goto done;
    }
    int present = reap_metadata(getpid(), &rows[0].info);
    if (present != 1) { reap_failed("self-metadata", getpid(), present < 0 ? errno : 0); goto done; }
    rows[0].nested = 1;
    for (unsigned at = 0; at < used; ++at) {
        if (!rows[at].nested) continue;
        pid_t owner = rows[at].info.ki_pid;
        struct kinfo_proc before, after;
        if (rows[at].depth >= REAP_DEPTH) { reap_failed("depth-limit", owner, 0); goto done; }
        if (!reap_within()) { reap_failed("owner-budget-or-signal", owner, 0); goto done; }
        present = reap_metadata(owner, &before);
        if (present != 1 || !reap_same(&before, &rows[at].info)) {
            reap_failed("owner-identity-before", owner, present < 0 ? errno : 0); goto done;
        }
        /* FreeBSD pfind() excludes zombies, but a zombie reaper retains its
         * descendants until proc_reap(). Never skip that unobserved branch. */
        if (before.ki_stat == SZOMB) {
            reap_failed("owner-zombie-unreaped", owner, 0); goto done;
        }
        unsigned count;
        struct procctl_reaper_pidinfo *children = reap_list(owner, &count);
        if (!children) goto done;
        int complete = 1;
        unsigned first_child = used;
        for (unsigned i = 0; i < count; ++i) {
            if (used > REAP_ROWS || !reap_within()) {
                reap_failed(used > REAP_ROWS ? "row-limit" : "member-budget-or-signal", owner, 0);
                complete = 0; break;
            }
            struct owned_row *r = &rows[used];
            int present = reap_metadata(children[i].pi_pid, &r->info);
            if (!present) continue; /* completed between ownership and metadata */
            if (present < 0) { reap_failed("member-metadata", children[i].pi_pid, errno); complete = 0; break; }
            r->reaper = owner;
            r->depth = rows[at].depth + 1;
            r->nested = !!(children[i].pi_flags & REAPER_PIDINFO_REAPER);
            if (!r->nested) {
                struct procctl_reaper_status s = {0};
                struct kinfo_proc check;
                int result = procctl(P_PID, r->info.ki_pid, PROC_REAP_STATUS, &s);
                if (result && errno == ESRCH) continue;
                int status_error = result ? errno : 0;
                int present_again = reap_metadata(r->info.ki_pid, &check);
                if (!present_again) continue;
                if (result || s.rs_reaper != owner || (s.rs_flags & REAPER_STATUS_OWNED) ||
                    present_again < 0 || !reap_same(&check, &r->info)) {
                    reap_failed("member-owner-or-identity", r->info.ki_pid,
                        status_error ? status_error : present_again < 0 ? errno : 0);
                    complete = 0; break;
                }
            }
            ++used;
        }
        free(children);
        if (!complete) goto done;
        /* Fresh parent membership plus matching birth on both sides admits
         * nested owners before they enter the queue. A later matching birth
         * preserves that identity; setsid/reaping cannot move a live process
         * into an unrelated reaper hierarchy. Stale/reused PIDs fail closed. */
        children = reap_list(owner, &count);
        if (!children) goto done;
        unsigned epoch = at + 1;
        for (unsigned i = 0; i < count; ++i) {
            pid_t pid = children[i].pi_pid;
            if (pid <= 0) { reap_failed("membership-pid", owner, 0); complete = 0; break; }
            unsigned slot = (unsigned)pid & (REAP_ROWS * 2 - 1);
            while (generation[slot] == epoch && membership[slot] != pid)
                slot = (slot + 1) & (REAP_ROWS * 2 - 1);
            membership[slot] = pid;
            generation[slot] = epoch;
        }
        free(children);
        if (!complete) goto done;
        for (unsigned i = first_child; i < used; ++i) {
            if (!rows[i].nested) continue;
            pid_t pid = rows[i].info.ki_pid;
            unsigned slot = (unsigned)pid & (REAP_ROWS * 2 - 1);
            while (generation[slot] == epoch && membership[slot] != pid)
                slot = (slot + 1) & (REAP_ROWS * 2 - 1);
            struct kinfo_proc confirmed;
            if (generation[slot] != epoch) { reap_failed("nested-membership-changed", pid, 0); goto done; }
            if (!reap_within()) { reap_failed("nested-budget-or-signal", pid, 0); goto done; }
            present = reap_metadata(pid, &confirmed);
            if (present != 1 || !reap_same(&confirmed, &rows[i].info)) {
                reap_failed("nested-identity", pid, present < 0 ? errno : 0); goto done;
            }
        }
        present = reap_metadata(owner, &after);
        if (present != 1 || !reap_same(&before, &after)) {
            reap_failed("owner-identity-after", owner, present < 0 ? errno : 0); goto done;
        }
    }
    size_t bytes = (size_t)snprintf(frame, REAP_FRAME, "SAMPLE 1 %d %d %d %u\n",
        getpid(), reap_payload, reap_status_raw, used);
    long page = sysconf(_SC_PAGESIZE);
    if (page <= 0 || page % 1024) { reap_failed("page-size", getpid(), 0); goto done; }
    for (unsigned i = 0; i < used; ++i) {
        struct kinfo_proc *p = &rows[i].info;
        if (p->ki_rssize < 0 || p->ki_start.tv_sec < 0 || p->ki_start.tv_usec < 0 ||
            p->ki_start.tv_usec >= 1000000 || bytes >= REAP_FRAME - 160) {
            reap_failed("sample-row-range", p->ki_pid, 0); goto done;
        }
        int n = snprintf(frame + bytes, REAP_FRAME - bytes,
            "%d %d %d %d %llu %d %lld %ld\n", p->ki_pid, p->ki_ppid, p->ki_pgid,
            p->ki_sid, (unsigned long long)p->ki_rssize * (unsigned long long)(page / 1024),
            p->ki_stat == SZOMB, (long long)p->ki_start.tv_sec, (long)p->ki_start.tv_usec);
        if (n <= 0 || n >= 160) { reap_failed("sample-row-size", p->ki_pid, 0); goto done; }
        bytes += (size_t)n;
    }
    memcpy(frame + bytes, "END\n", 4); bytes += 4;
    if (reap_within()) {
        ok = reap_write(output, frame, bytes, reap_deadline) ? 1 : -1;
        if (ok < 0) reap_failed("sample-write-incomplete", getpid(), 0);
    } else reap_failed("sample-budget-or-signal", getpid(), 0);
done:
    free(rows); free(frame); free(membership); free(generation);
    return ok;
}
static int reap_sample(int output, unsigned budget_ms) {
    reap_deadline = reap_clock() + budget_ms / 1000.0;
    reap_failed("sample-budget-or-signal", getpid(), 0);
    /* A subordinate reaper can finish between two metadata reads. Drain
     * waitable children before each complete observation: a zombie reaper can
     * retain descendants while procctl rejects its PID. Reaping transfers
     * those descendants; only the fresh traversal may admit them. A zombie
     * owned by another parent still fails closed. Never reset the budget or
     * accept a partial branch. Attempted reply bytes terminate on failure. */
    unsigned attempts = 0;
    for (; attempts < 3 && reap_within();) {
        ++attempts;
        reap_wait(); /* Existing 256-wait / 2-ms bound, inside this deadline. */
        if (!reap_within()) {
            reap_failed("sample-budget-or-signal", getpid(), 0); break;
        }
        int result = reap_sample_once(output);
        if (result > 0) return 1;
        if (result < 0) break;
    }
    reap_report(output, "sample", reap_failure, reap_failure_pid, reap_failure_errno, attempts, -1);
    return 0;
}
static int reap_number(const char *s, unsigned max, unsigned *value) {
    unsigned n = 0;
    if (!s || !*s) return 0;
    for (; *s; ++s) {
        if (*s < '0' || *s > '9' || n > (max - (unsigned)(*s - '0')) / 10) return 0;
        n = n * 10 + (unsigned)(*s - '0');
    }
    *value = n; return 1;
}
static int reaper_owner(int argc, char **argv) {
    unsigned input, output, budget;
    if (argc < 7 || strcmp(argv[5], "--") ||
        !reap_number(argv[2], INT_MAX, &input) || input < 3 ||
        !reap_number(argv[3], INT_MAX, &output) || output < 3 || input == output ||
        !reap_number(argv[4], 30000, &budget) || budget < 1000) return reject("invalid reaper owner arguments");
    pid_t parent = getppid();
    struct sigaction sa = {0};
    sa.sa_handler = reap_interrupted;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGTERM, &sa, NULL) || sigaction(SIGINT, &sa, NULL) ||
        sigaction(SIGHUP, &sa, NULL)) return reject("reaper signal setup failed");
    signal(SIGPIPE, SIG_IGN);
    int parent_signal = SIGTERM;
    if (procctl(P_PID, 0, PROC_PDEATHSIG_CTL, &parent_signal) || getppid() != parent ||
        procctl(P_PID, 0, PROC_REAP_ACQUIRE, NULL) || !reap_owned(getpid()))
        return reject("reaper acquisition failed");
    struct kinfo_proc owner_identity;
    if (reap_metadata(getpid(), &owner_identity) != 1) return reject("reaper identity unavailable");
    int output_flags = fcntl((int)output, F_GETFL);
    if (output_flags < 0 || fcntl((int)output, F_SETFL, output_flags | O_NONBLOCK))
        return reject("reaper output setup failed");
    int gate[2];
    if (pipe(gate)) return reject("reaper gate failed");
    reap_payload = fork();
    if (reap_payload < 0) { close(gate[0]); close(gate[1]); return reject("reaper fork failed"); }
    if (!reap_payload) {
        close((int)input); close((int)output); close(gate[1]);
        signal(SIGTERM, SIG_DFL); signal(SIGINT, SIG_DFL); signal(SIGHUP, SIG_DFL);
        signal(SIGPIPE, SIG_DFL);
        if (setpgid(0, 0)) _exit(89);
        char start;
        if (read(gate[0], &start, 1) != 1 || start != 'G') _exit(89);
        close(gate[0]);
        execvp(argv[6], argv + 6);
        _exit(127);
    }
    close(gate[0]);
    int released = 0, requested = 0, failed = 0, failure_errno = 0;
    const char *exit_reason = "parent-or-signal";
    while (!reap_stop && getppid() == parent) {
        reap_wait();
        struct pollfd p = {(int)input, POLLIN, 0};
        int rc = poll(&p, 1, 20);
        if (rc < 0 && errno == EINTR) continue;
        if (rc < 0) { exit_reason = "command-poll"; failure_errno = errno; failed = 1; break; }
        if (!rc) continue;
        char command;
        ssize_t received = read((int)input, &command, 1);
        if (received != 1) {
            exit_reason = received < 0 ? "command-read" : "command-eof";
            failure_errno = received < 0 ? errno : 0; failed = 1; break;
        }
        if (command == 'G' && !released) {
            if (write(gate[1], "G", 1) != 1) {
                exit_reason = "payload-gate"; failure_errno = errno; failed = 1; break;
            }
            close(gate[1]); gate[1] = -1; released = 1;
        } else if (command == 'S') {
            if (!reap_sample((int)output, budget)) { exit_reason = "sample-failed"; failed = 1; break; }
        } else if (command == 'T') {
            if (!reap_signal_all(SIGTERM) ||
                !reap_write((int)output, "TERM 1\n", 7, reap_clock() + budget / 1000.0)) {
                exit_reason = "term-signal-or-reply"; failed = 1; break;
            }
        } else if (command == 'Q') { exit_reason = "cleanup-requested"; requested = 1; break; }
        else { exit_reason = "invalid-command"; failed = 1; break; }
    }
    if (gate[1] >= 0) close(gate[1]);
    int quiet = reap_cleanup();
    if (requested) {
        char reply[160];
        int n = snprintf(reply, sizeof(reply), "QUIET %d %d %d %lld %ld\n", quiet, reap_status_raw,
            getpid(), (long long)owner_identity.ki_start.tv_sec, (long)owner_identity.ki_start.tv_usec);
        if (!reap_write((int)output, reply, (size_t)n, reap_clock() + 1.0)) {
            exit_reason = "cleanup-reply"; failed = 1;
        }
    }
    if (failed || !quiet || !requested)
        reap_report((int)output, "stop", exit_reason, getppid(), failure_errno, 0, quiet);
    close((int)input); close((int)output);
    /* Losing the control peer or exhausting one cleanup attempt must not
     * abandon live descendants. Retain the kernel owner and retry at low duty
     * cycle; the parent already reports QUIET 0 and this exact owner's identity.
     * Each attempt remains bounded. Signals cannot turn this into a busy loop. */
    while (!quiet) {
        double retry_at = reap_clock() + 5.0;
        while (reap_clock() < retry_at) {
            double left = retry_at - reap_clock();
            if (left <= 0) break;
            struct timespec pause = {(time_t)left, (long)((left - (time_t)left) * 1000000000.0)};
            nanosleep(&pause, NULL);
        }
        quiet = reap_cleanup();
    }
    return quiet && !failed && requested ? 0 : 89;
}
#endif

int main(int argc, char **argv) {
#ifdef __FreeBSD__
    if (argc >= 2 && !strcmp(argv[1], "--reaper-owner")) return reaper_owner(argc, argv);
#endif
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
