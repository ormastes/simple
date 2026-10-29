/* Private Windows V2 lease owner. Included after the synchronous Win32 helpers.
 * V3 atomic stdin, sealed pins, and the V4 wire remain unsupported. A live
 * HANDLE and Job Object are authority; diagnostic PIDs never authorize work.
 * The registry lock protects every slot/handle access. Poll releases it before
 * sleeping, so independent leases and collection can continue concurrently. */
#define OWNED_WIN_ASYNC_SLOTS 128
#define OWNED_WIN_ASYNC_MAX_WAIT_MS 250

typedef struct OwnedWinLease {
    int used; /* 1: published, 2: rejected start still owned until exact wait */
    RtOwnedProcessTokenV2 token;
    HANDLE process, job;
    DWORD pid;
    uint64_t identity;
    ULONGLONG started, reaped_at;
    int64_t timeout_ms;
    uint64_t capture_limit, out_delivered, err_delivered;
    OwnedWinStream out, err;
    int reaped, terminal, cancel_requested, timed_out, kill_sent, op_refs;
    int runtime_error;
    int64_t exit_code;
} OwnedWinLease;

static SRWLOCK owned_win_leases_lock = SRWLOCK_INIT;
static OwnedWinLease owned_win_leases[OWNED_WIN_ASYNC_SLOTS];

static void owned_win_lease_dispose(OwnedWinLease* slot) {
    owned_win_close(&slot->job); /* KILL_ON_JOB_CLOSE remains armed. */
    owned_win_close(&slot->process);
    owned_win_close(&slot->out.read_end);
    owned_win_close(&slot->out.write_end);
    owned_win_close(&slot->err.read_end);
    owned_win_close(&slot->err.write_end);
    RT_OWNED_HOST_FREE(slot->out.buf);
    RT_OWNED_HOST_FREE(slot->err.buf);
    memset(slot, 0, sizeof(*slot));
}

static OwnedWinLease* owned_win_lease_find(RtOwnedProcessTokenV2 token) {
    if (!token.high && !token.low) return NULL;
    for (int i = 0; i < OWNED_WIN_ASYNC_SLOTS; i++) {
        OwnedWinLease* slot = &owned_win_leases[i];
        if (slot->used == 1 && slot->token.high == token.high && slot->token.low == token.low)
            return slot;
    }
    return NULL;
}

static int owned_win_random_token(RtOwnedProcessTokenV2* token) {
    /* RtlGenRandom is the OS CSPRNG. Resolve dynamically to avoid adding a
     * linker dependency to the many standalone runtime consumers. */
    typedef BOOLEAN (WINAPI *OwnedWinRandom)(PVOID, ULONG);
    HMODULE module = LoadLibraryW(L"advapi32.dll");
    if (!module) return 0;
    OwnedWinRandom random = (OwnedWinRandom)(void*)GetProcAddress(module, "SystemFunction036");
    int ok = random && random(token, (ULONG)sizeof(*token));
    FreeLibrary(module);
    return ok;
}

static void owned_win_lease_error(OwnedWinLease* slot, int error) {
    if (!slot->runtime_error) slot->runtime_error = error;
}

static int owned_win_lease_kill(OwnedWinLease* slot) {
    if (slot->kill_sent) return 1;
    if (!TerminateJobObject(slot->job, 1)) {
        owned_win_lease_error(slot, EIO);
        return 0;
    }
    slot->kill_sent = 1;
    return 1;
}

static void owned_win_lease_drain(OwnedWinLease* slot, OwnedWinStream* stream,
                                  const OwnedWinStream* other) {
    if (!stream->read_end) return;
    /* The V2 cap is shared across both streams; delivery never frees policy
     * space. Each poll uses a finite quantum for each stream. */
    stream->limit = slot->capture_limit - other->kept;
    DWORD budget = 64U * 1024U;
    while (budget) {
        DWORD available = 0;
        if (!PeekNamedPipe(stream->read_end, NULL, 0, NULL, &available, NULL)) {
            DWORD error = GetLastError();
            if (error != ERROR_BROKEN_PIPE) owned_win_lease_error(slot, EIO);
            owned_win_close(&stream->read_end);
            return;
        }
        if (!available) return;
        char chunk[4096];
        DWORD want = available < sizeof(chunk) ? available : (DWORD)sizeof(chunk);
        if (want > budget) want = budget;
        DWORD got = 0;
        if (!ReadFile(stream->read_end, chunk, want, &got, NULL) || !got) {
            if (GetLastError() != ERROR_BROKEN_PIPE) owned_win_lease_error(slot, EIO);
            owned_win_close(&stream->read_end);
            return;
        }
        budget -= got;
        stream->seen = UINT64_MAX - stream->seen < got ? UINT64_MAX : stream->seen + got;
        uint64_t room = stream->limit - stream->kept;
        uint64_t take = got < room ? got : room;
        if (take) memcpy(stream->buf + stream->kept, chunk, (size_t)take);
        stream->kept += take;
        if (take < got) stream->truncated = 1;
    }
}

static void owned_win_lease_advance(OwnedWinLease* slot) {
    if (slot->terminal) return;
    owned_win_lease_drain(slot, &slot->out, &slot->err);
    owned_win_lease_drain(slot, &slot->err, &slot->out);
    ULONGLONG now = GetTickCount64();
    if (!slot->reaped) {
        DWORD waited = WaitForSingleObject(slot->process, 0);
        if (waited == WAIT_OBJECT_0) {
            DWORD code = 0;
            if (GetExitCodeProcess(slot->process, &code)) {
                /* 259 is a legitimate exit code after an exact signalled wait. */
                slot->exit_code = (int64_t)(int32_t)code;
                slot->reaped = 1;
                slot->reaped_at = now;
            } else owned_win_lease_error(slot, EIO);
        } else if (waited == WAIT_FAILED) owned_win_lease_error(slot, EIO);
    }
    JOBOBJECT_BASIC_ACCOUNTING_INFORMATION accounting;
    memset(&accounting, 0, sizeof(accounting));
    int accounting_ok = QueryInformationJobObject(slot->job, JobObjectBasicAccountingInformation,
        &accounting, sizeof(accounting), NULL) != 0;
    if (!accounting_ok) owned_win_lease_error(slot, EIO);
    if (!slot->reaped && !slot->kill_sent &&
        (slot->cancel_requested || (slot->timeout_ms > 0 && now - slot->started >= (ULONGLONG)slot->timeout_ms))) {
        slot->timed_out = !slot->cancel_requested;
        (void)owned_win_lease_kill(slot);
    }
    /* Once the leader exits, descendants cannot retain a lease indefinitely.
     * Require observed zero active job processes before claiming terminal. */
    if (slot->reaped && accounting_ok && accounting.ActiveProcesses && !slot->kill_sent)
        (void)owned_win_lease_kill(slot);
    if (slot->reaped && now - slot->reaped_at >= RT_OWNED_POST_REAP_DRAIN_MS) {
        if (slot->out.read_end) { slot->out.truncated = 1; owned_win_close(&slot->out.read_end); }
        if (slot->err.read_end) { slot->err.truncated = 1; owned_win_close(&slot->err.read_end); }
    }
    if (slot->reaped && accounting_ok && !accounting.ActiveProcesses &&
        !slot->out.read_end && !slot->err.read_end) slot->terminal = 1;
}

bool rt_process_owned_start_v2(const char* cmd, const char* const* argv,
                               int64_t timeout_ms, int64_t term_grace_ms,
                               uint64_t max_output_bytes, RtOwnedProcessTokenV2* token,
                               RtOwnedProcessStartReceiptV2* receipt) {
    if (!receipt || !token) return false;
    memset(token, 0, sizeof(*token)); memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
    if (!cmd || !cmd[0] || !argv || !argv[0] || timeout_ms < 0 || term_grace_ms < 0 ||
        max_output_bytes > RT_OWNED_ABI_MAX_OUTPUT_BYTES) {
        receipt->runtime_error = EINVAL; return false;
    }
    if (timeout_ms > RT_OWNED_ABI_MAX_TIMEOUT_MS) timeout_ms = RT_OWNED_ABI_MAX_TIMEOUT_MS;
    AcquireSRWLockExclusive(&owned_win_leases_lock);
    OwnedWinLease* slot = NULL;
    for (int i = 0; i < OWNED_WIN_ASYNC_SLOTS; i++) {
        OwnedWinLease* candidate = &owned_win_leases[i];
        if (candidate->used == 2 && WaitForSingleObject(candidate->process, 0) == WAIT_OBJECT_0)
            owned_win_lease_dispose(candidate);
        if (!candidate->used && !slot) slot = candidate;
    }
    int error = 0;
    HANDLE stdin_handle = NULL;
    PROCESS_INFORMATION child; memset(&child, 0, sizeof(child));
    char* command = NULL; WCHAR* wide_command = NULL; WCHAR* application = NULL;
    LPPROC_THREAD_ATTRIBUTE_LIST attributes = NULL;
    if (!slot) { error = EAGAIN; goto done; }
    memset(slot, 0, sizeof(*slot)); slot->used = 2; slot->exit_code = -1;
    for (int attempts = 0; attempts < 8; attempts++) {
        if (!owned_win_random_token(&slot->token)) { error = EIO; goto done; }
        if ((slot->token.high || slot->token.low) && !owned_win_lease_find(slot->token)) break;
        memset(&slot->token, 0, sizeof(slot->token));
    }
    if (!slot->token.high && !slot->token.low) { error = EAGAIN; goto done; }
    slot->timeout_ms = timeout_ms; slot->capture_limit = max_output_bytes;
    slot->out.cap = slot->err.cap = max_output_bytes + 1;
    slot->out.buf = (char*)RT_OWNED_HOST_MALLOC((size_t)slot->out.cap);
    slot->err.buf = (char*)RT_OWNED_HOST_MALLOC((size_t)slot->err.cap);
    if (!slot->out.buf || !slot->err.buf) { error = ENOMEM; goto done; }
    SECURITY_ATTRIBUTES security = {sizeof(security), NULL, TRUE};
    if (!CreatePipe(&slot->out.read_end, &slot->out.write_end, &security, 0) ||
        !CreatePipe(&slot->err.read_end, &slot->err.write_end, &security, 0) ||
        !SetHandleInformation(slot->out.read_end, HANDLE_FLAG_INHERIT, 0) ||
        !SetHandleInformation(slot->err.read_end, HANDLE_FLAG_INHERIT, 0)) { error = EMFILE; goto done; }
    stdin_handle = CreateFileW(L"NUL", GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE,
        &security, OPEN_EXISTING, 0, NULL);
    if (stdin_handle == INVALID_HANDLE_VALUE) { error = EIO; goto done; }
    slot->job = CreateJobObjectW(NULL, NULL);
    JOBOBJECT_EXTENDED_LIMIT_INFORMATION limits; memset(&limits, 0, sizeof(limits));
    limits.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
    if (!slot->job || !SetInformationJobObject(slot->job, JobObjectExtendedLimitInformation,
        &limits, sizeof(limits))) { error = EIO; goto done; }
    command = owned_win_build_cmdline(argv);
    if (!command || !(wide_command = owned_win_widen(command))) { error = ENOMEM; goto done; }
    application = owned_win_resolve_exe(cmd);
    /* Do not let CreateProcess silently execute argv[0] instead of cmd. Bare
     * commands use an explicit PATH resolution; unresolved paths fail closed. */
    if (!application) {
        WCHAR* requested = owned_win_widen(cmd);
        if (!requested) { error = EINVAL; goto done; }
        DWORD size = SearchPathW(NULL, requested, L".exe", 0, NULL, NULL);
        if (size) {
            application = (WCHAR*)RT_OWNED_HOST_MALLOC(((size_t)size + 1) * sizeof(WCHAR));
            if (application) {
                DWORD written = SearchPathW(NULL, requested, L".exe", size + 1, application, NULL);
                if (!written || written > size) {
                    RT_OWNED_HOST_FREE(application); application = NULL;
                }
            }
        }
        RT_OWNED_HOST_FREE(requested);
        if (!application) { error = ENOENT; goto done; }
    }
    SIZE_T size = 0;
    InitializeProcThreadAttributeList(NULL, 1, 0, &size);
    attributes = (LPPROC_THREAD_ATTRIBUTE_LIST)RT_OWNED_HOST_MALLOC(size);
    if (!attributes) { error = ENOMEM; goto done; }
    if (!InitializeProcThreadAttributeList(attributes, 1, 0, &size)) {
        RT_OWNED_HOST_FREE(attributes); attributes = NULL; error = EIO; goto done;
    }
    HANDLE inherited[] = {stdin_handle, slot->out.write_end, slot->err.write_end};
    if (!UpdateProcThreadAttribute(attributes, 0, PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
        inherited, sizeof(inherited), NULL, NULL)) { error = EIO; goto done; }
    STARTUPINFOEXW startup; memset(&startup, 0, sizeof(startup));
    startup.StartupInfo.cb = sizeof(startup); startup.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    startup.StartupInfo.hStdInput = stdin_handle;
    startup.StartupInfo.hStdOutput = slot->out.write_end;
    startup.StartupInfo.hStdError = slot->err.write_end;
    startup.lpAttributeList = attributes;
    slot->started = GetTickCount64();
    if (!CreateProcessW(application, wide_command, NULL, NULL, TRUE,
        EXTENDED_STARTUPINFO_PRESENT | CREATE_SUSPENDED | CREATE_NO_WINDOW,
        NULL, NULL, &startup.StartupInfo, &child)) {
        DWORD last = GetLastError();
        error = last == ERROR_FILE_NOT_FOUND || last == ERROR_PATH_NOT_FOUND ? ENOENT :
            last == ERROR_ACCESS_DENIED ? EACCES : EIO;
        goto done;
    }
    slot->process = child.hProcess; slot->pid = child.dwProcessId;
    FILETIME creation, exit_time, kernel, user;
    if (!GetProcessTimes(slot->process, &creation, &exit_time, &kernel, &user)) { error = EIO; goto done; }
    slot->identity = ((uint64_t)creation.dwHighDateTime << 32) | creation.dwLowDateTime;
    if (!AssignProcessToJobObject(slot->job, slot->process)) { error = EPERM; goto done; }
    if (ResumeThread(child.hThread) == (DWORD)-1) { error = EIO; goto done; }
    slot->used = 1; *token = slot->token; receipt->accepted = 1;
done:
    owned_win_close(&child.hThread);
    owned_win_close(&stdin_handle);
    if (attributes) { DeleteProcThreadAttributeList(attributes); RT_OWNED_HOST_FREE(attributes); }
    RT_OWNED_HOST_FREE(command); RT_OWNED_HOST_FREE(wide_command); RT_OWNED_HOST_FREE(application);
    if (slot) {
        owned_win_close(&slot->out.write_end); owned_win_close(&slot->err.write_end);
        if (error) {
            /* A failed admission cannot relinquish a suspended live process.
             * Retain its HANDLE privately if termination/wait has not finished. */
            if (slot->process) {
                (void)TerminateProcess(slot->process, 1);
                owned_win_close(&slot->job);
                if (WaitForSingleObject(slot->process, 2000) == WAIT_OBJECT_0)
                    owned_win_lease_dispose(slot);
            } else owned_win_lease_dispose(slot);
        }
    }
    receipt->runtime_error = error;
    ReleaseSRWLockExclusive(&owned_win_leases_lock);
    return error == 0;
}

static uint64_t owned_win_lease_deliver(OwnedWinStream* stream, uint64_t* delivered,
                                       char* output, uint64_t capacity) {
    if (!capacity) return 0;
    uint64_t count = stream->kept - *delivered;
    if (count > capacity - 1) count = capacity - 1;
    if (count) memcpy(output, stream->buf + *delivered, (size_t)count);
    *delivered += count; output[count] = 0;
    return count;
}

static void owned_win_lease_poll_receipt(const OwnedWinLease* slot,
                                         RtOwnedProcessPollReceiptV2* receipt,
                                         uint64_t out_count, uint64_t err_count) {
    receipt->live = !slot->terminal; receipt->terminal = slot->terminal;
    receipt->cancel_requested = slot->cancel_requested; receipt->timed_out = slot->timed_out;
    receipt->term_sent = receipt->kill_sent = slot->kill_sent; receipt->reaped = slot->reaped;
    receipt->stdout_truncated = slot->out.truncated; receipt->stderr_truncated = slot->err.truncated;
    receipt->stdout_bytes_seen = slot->out.seen; receipt->stderr_bytes_seen = slot->err.seen;
    receipt->stdout_bytes_kept = slot->out.kept; receipt->stderr_bytes_kept = slot->err.kept;
    receipt->stdout_bytes_delivered = out_count; receipt->stderr_bytes_delivered = err_count;
    receipt->runtime_error = slot->runtime_error;
}

bool rt_process_owned_poll_v2(RtOwnedProcessTokenV2 token, int64_t wait_ms,
                              char* out, uint64_t out_cap, char* err, uint64_t err_cap,
                              RtOwnedProcessPollReceiptV2* receipt) {
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt)); receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
    if (wait_ms < 0 || (out_cap && !out) || (err_cap && !err)) {
        receipt->runtime_error = EINVAL; return false;
    }
    if (out_cap) out[0] = 0;
    if (err_cap) err[0] = 0;
    if (wait_ms > OWNED_WIN_ASYNC_MAX_WAIT_MS) wait_ms = OWNED_WIN_ASYNC_MAX_WAIT_MS;
    ULONGLONG until = GetTickCount64() + (ULONGLONG)wait_ms;
    AcquireSRWLockExclusive(&owned_win_leases_lock);
    OwnedWinLease* slot = owned_win_lease_find(token);
    if (!slot) {
        ReleaseSRWLockExclusive(&owned_win_leases_lock);
        receipt->runtime_error = RT_OWNED_PROCESS_WINDOWS_STALE_ERROR; return false;
    }
    slot->op_refs++;
    ReleaseSRWLockExclusive(&owned_win_leases_lock);
    for (;;) {
        AcquireSRWLockExclusive(&owned_win_leases_lock);
        owned_win_lease_advance(slot);
        uint64_t out_count = owned_win_lease_deliver(&slot->out, &slot->out_delivered, out, out_cap);
        uint64_t err_count = owned_win_lease_deliver(&slot->err, &slot->err_delivered, err, err_cap);
        owned_win_lease_poll_receipt(slot, receipt, out_count, err_count);
        int done = out_count || err_count || slot->terminal || GetTickCount64() >= until;
        if (done) slot->op_refs--;
        ReleaseSRWLockExclusive(&owned_win_leases_lock);
        if (done) return receipt->runtime_error == 0;
        Sleep(1);
    }
}

static void owned_win_lease_result(const OwnedWinLease* slot, RtOwnedProcessResultV2* result) {
    result->pid = result->process_group_id = slot->pid;
    result->start_identity = slot->identity; result->exit_code = slot->exit_code;
    result->timed_out = slot->timed_out; result->cancel_requested = slot->cancel_requested;
    result->term_sent = result->kill_sent = slot->kill_sent;
    result->identity_revalidated = slot->reaped; result->reaped = slot->reaped;
    result->stdout_truncated = slot->out.truncated; result->stderr_truncated = slot->err.truncated;
    result->stdout_bytes_seen = slot->out.seen; result->stderr_bytes_seen = slot->err.seen;
    result->stdout_bytes_kept = slot->out.kept; result->stderr_bytes_kept = slot->err.kept;
    result->runtime_error = slot->runtime_error;
}

static bool owned_win_lease_get_result(RtOwnedProcessTokenV2 token,
                                       RtOwnedProcessResultV2* result, int collect) {
    if (!result) return false;
    memset(result, 0, sizeof(*result)); result->version = RT_OWNED_PROCESS_ASYNC_VERSION;
    result->exit_code = -1;
    AcquireSRWLockExclusive(&owned_win_leases_lock);
    OwnedWinLease* slot = owned_win_lease_find(token);
    if (!slot) result->runtime_error = RT_OWNED_PROCESS_WINDOWS_STALE_ERROR;
    else if (collect && slot->op_refs) result->runtime_error = EBUSY;
    else if (!slot->terminal) result->runtime_error = EAGAIN;
    else if (collect && (slot->out_delivered != slot->out.kept || slot->err_delivered != slot->err.kept))
        result->runtime_error = EBUSY;
    else {
        owned_win_lease_result(slot, result);
        /* Terminal provider errors are result data, not authority to leak. */
        if (collect) owned_win_lease_dispose(slot);
    }
    ReleaseSRWLockExclusive(&owned_win_leases_lock);
    return result->runtime_error == 0;
}

bool rt_process_owned_result_v2(RtOwnedProcessTokenV2 token, RtOwnedProcessResultV2* result) {
    return owned_win_lease_get_result(token, result, 0);
}
bool rt_process_owned_collect_v2(RtOwnedProcessTokenV2 token, RtOwnedProcessResultV2* result) {
    return owned_win_lease_get_result(token, result, 1);
}

bool rt_process_owned_cancel_v2(RtOwnedProcessTokenV2 token, RtOwnedProcessCancelReceipt* receipt) {
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt)); receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
    AcquireSRWLockExclusive(&owned_win_leases_lock);
    OwnedWinLease* slot = owned_win_lease_find(token);
    if (!slot) {
        receipt->runtime_error = RT_OWNED_PROCESS_WINDOWS_STALE_ERROR;
        ReleaseSRWLockExclusive(&owned_win_leases_lock); return false;
    }
    receipt->pid = slot->pid; receipt->start_identity = slot->identity; receipt->accepted = 1;
    slot->op_refs++;
    if (!slot->terminal) slot->cancel_requested = 1;
    ReleaseSRWLockExclusive(&owned_win_leases_lock);
    ULONGLONG until = GetTickCount64() + 2000;
    RtOwnedProcessPollReceiptV2 poll;
    do {
        (void)rt_process_owned_poll_v2(token, 10, NULL, 0, NULL, 0, &poll);
        receipt->term_sent = poll.term_sent; receipt->runtime_error = poll.runtime_error;
        if (poll.terminal) break;
    } while (GetTickCount64() < until);
    if (!poll.terminal && !receipt->runtime_error) receipt->runtime_error = ETIMEDOUT;
    AcquireSRWLockExclusive(&owned_win_leases_lock);
    slot->op_refs--;
    ReleaseSRWLockExclusive(&owned_win_leases_lock);
    return poll.terminal && receipt->runtime_error == 0;
}

bool rt_process_owned_observation_v1(RtOwnedProcessTokenV2 token,
                                     RtOwnedProcessObservationV1* observation) {
    if (!observation) return false;
    memset(observation, 0, sizeof(*observation));
    observation->version = RT_OWNED_PROCESS_OBSERVATION_VERSION;
    AcquireSRWLockExclusive(&owned_win_leases_lock);
    OwnedWinLease* slot = owned_win_lease_find(token);
    if (!slot) observation->runtime_error = RT_OWNED_PROCESS_WINDOWS_STALE_ERROR;
    else if (!slot->terminal) observation->runtime_error = EAGAIN;
    else {
        /* Optional resource evidence remains unavailable here. Job commit is
         * not RSS and lifetime TotalProcesses is not peak concurrency. */
        if (!slot->out.truncated && !slot->err.truncated && !slot->runtime_error)
            observation->evidence_flags = RT_PROCESS_EVIDENCE_OUTPUT_EOF;
        observation->runtime_error = slot->runtime_error;
    }
    ReleaseSRWLockExclusive(&owned_win_leases_lock);
    return observation->runtime_error == 0;
}

#define RT_OWNED_WIN32_ASYNC_IMPLEMENTED 1
