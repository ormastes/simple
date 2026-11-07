/* InteractiveV1 is a mode of owned_win_leases and owned_win_v3_slots.
 * This header is included once, at the end of runtime_process_owned.c.
 * No process identity or authority is stored outside those canonical slots. */
#include "runtime_process_interactive_v1_abi.h"

static int oiv1_output(Oiv1Receipt* out, uint64_t size) {
    if (!out || size != sizeof(*out)) return 0;
    memset(out, 0, sizeof(*out)); out->version=1; out->size=sizeof(*out); return 1;
}
static int oiv1_request(const void* request, uint64_t actual, uint64_t expected) {
    if (!request || actual != expected) return 0;
    const uint64_t* words=(const uint64_t*)request;
    return words[0]==1 && words[1]==expected;
}
static int64_t oiv1_invalid(Oiv1Receipt* out) {
    out->status=OIV1_STATUS_INVALIDARGUMENT;
    out->error_domain=OIV1_ERROR_CONTRACT; out->validity_mask=OIV1_VALID_ERROR;
    return 0;
}

#if defined(_WIN32) && defined(RT_OWNED_WIN32_V3_ADAPTER)
#ifndef PROC_THREAD_ATTRIBUTE_JOB_LIST
#define PROC_THREAD_ATTRIBUTE_JOB_LIST 0x0002000D
#endif

typedef struct Oiv1Ring {
    uint8_t* bytes;
    uint64_t capacity, head, count, seen, delivered, discarded;
    uint64_t state;
    HANDLE parent, child;
    OVERLAPPED io;
    uint8_t pending_bytes[4096];
    DWORD requested;
    int pending;
} Oiv1Ring;
typedef struct Oiv1Segment { uint64_t count; int64_t expires_ms; } Oiv1Segment;
typedef struct Oiv1State {
    SRWLOCK lock;
    uint32_t core_index, adapter_index;
    uint64_t handle, generation, phase, sequence;
    Oiv1Deadline startup;
    char** argv;
    WCHAR* application;
    WCHAR* commandline;
    Oiv1Ring input, output, error;
    Oiv1Segment segments[256];
    uint32_t segment_head, segment_count;
    uint64_t accepted, written, stdin_state;
    uint64_t error_domain, error_code, exit_kind, exit_value;
    uint64_t flags;
    HANDLE wake, unused_wake;
    int wake_registered;
    HANDLE child_input, process, thread, job;
    OVERLAPPED input_io;
    DWORD input_requested;
    int input_pending, finish_requested, cancel_requested, collect_requested, discard;
    int input_progress_uncertain;
    int kill_sent;
    int startup_refusal;
    volatile LONG worker_done, start_decision, delivery_decision;
    volatile LONG worker_cancel;
    uint64_t delivery_out, delivery_err, ticket_kind, ticket_sequence, ticket_seal;
} Oiv1State;
#ifdef SIMPLE_RUNTIME_INTERACTIVE_V1_TEST_HOOKS
static volatile LONG oiv1_test_submit_failures;
static HANDLE oiv1_test_created_entered, oiv1_test_created_release;
static HANDLE oiv1_test_poll_wait_entered, oiv1_test_poll_wait_release;
void simple_owned_interactive_v1_test_fail_submissions(LONG count) {
    InterlockedExchange(&oiv1_test_submit_failures,count);
}
void simple_owned_interactive_v1_test_created_gate(HANDLE entered,HANDLE release) {
    oiv1_test_created_entered=entered; oiv1_test_created_release=release;
}
void simple_owned_interactive_v1_test_poll_wait_gate(HANDLE entered,HANDLE release) {
    oiv1_test_poll_wait_entered=entered; oiv1_test_poll_wait_release=release;
}
#endif

static void oiv1_free_unpublished(Oiv1State* s);
/* Retired allocation only, never a process authority or another registry.
 * It is freed immediately after releasing both existing owner locks. */
static _Thread_local Oiv1State* oiv1_retired_memory;
static void oiv1_failed_submission_maintenance(void) {
    for (uint32_t c=0;c<128;c++) {
        OwnedWinLease* core=&owned_win_leases[c];
        if (core->used!=3 || InterlockedCompareExchange(&core->interactive_refs,0,0) ||
            ((uint64_t)InterlockedCompareExchange64(&core->interactive_intent,0,0)&3)!=2) continue;
        Oiv1State* s=(Oiv1State*)core->interactive_state;
        if (!s || !TryAcquireSRWLockExclusive(&s->lock)) continue;
        OwnedWinV3Slot* adapter=&owned_win_v3_slots[s->adapter_index];
        if (s->phase!=OIV1_PHASE_FAILEDHELD || !InterlockedCompareExchange(&s->worker_done,0,0) ||
            !(s->flags&OIV1_FLAG_NOCHILDPROVEN) || !(s->flags&OIV1_FLAG_RESOURCESCLOSED) ||
            InterlockedCompareExchange(&adapter->interactive_refs,0,0)) {
            ReleaseSRWLockExclusive(&s->lock); continue;
        }
        /* A failed submission never made a child or I/O. The ABORT is settled
         * and all references are gone. Recycle metadata, not live resources. */
        InterlockedExchange64(&core->interactive_intent,0); InterlockedExchange64(&core->interactive_seal,0);
        core->interactive_state=NULL; core->used=0; memset(adapter,0,sizeof(*adapter));
        ReleaseSRWLockExclusive(&s->lock); oiv1_retired_memory=s; return;
    }
}

static int oiv1_expired(Oiv1Deadline d) {
    return d.clock_tag!=OIV1_CLOCK_WINDOWS || d.expires_ms<0 ||
        (uint64_t)d.expires_ms <= GetTickCount64();
}
static void oiv1_drop(OwnedWinLease* core, OwnedWinV3Slot* adapter) {
    /* Last access to each entry precedes its release: never take a lock here. */
    InterlockedDecrement(&core->interactive_refs);
    InterlockedDecrement(&adapter->interactive_refs);
}
static void oiv1_unlock(void) {
    ReleaseSRWLockExclusive(&owned_win_leases_lock);
    ReleaseSRWLockExclusive(&owned_win_v3_lock);
    Oiv1State* retired=oiv1_retired_memory; oiv1_retired_memory=NULL;
    if (retired) oiv1_free_unpublished(retired);
}
static int oiv1_locks(Oiv1Receipt* receipt) {
    if (!TryAcquireSRWLockExclusive(&owned_win_v3_lock)) goto busy;
    if (!TryAcquireSRWLockExclusive(&owned_win_leases_lock)) {
        ReleaseSRWLockExclusive(&owned_win_v3_lock); goto busy;
    }
    oiv1_failed_submission_maintenance();
    return 1;
busy:
    receipt->status=OIV1_STATUS_BUSY; receipt->flags=OIV1_FLAG_LOCKCONTENDED;
    return 0;
}
static void oiv1_legacy_unlocked_maintenance(void) {
    Oiv1Receipt ignored; oiv1_output(&ignored,sizeof(ignored));
    if (oiv1_locks(&ignored)) oiv1_unlock();
}
static Oiv1State* oiv1_take(int64_t handle, Oiv1Receipt* receipt,
                          OwnedWinLease** core_out, OwnedWinV3Slot** adapter_out) {
    if (!oiv1_locks(receipt)) return NULL;
    for (uint32_t a=0;a<OWNED_WIN_V3_SLOTS;a++) {
        OwnedWinV3Slot* adapter=&owned_win_v3_slots[a];
        if (!adapter->active || !adapter->interactive_mode || adapter->handle!=(uint64_t)handle) continue;
        for (uint32_t c=0;c<OWNED_WIN_ASYNC_SLOTS;c++) {
            OwnedWinLease* core=&owned_win_leases[c];
            if (core->used!=3 || !core->interactive_state ||
                core->token.high!=adapter->token.high || core->token.low!=adapter->token.low) continue;
            Oiv1State* state=(Oiv1State*)core->interactive_state;
            if (!TryAcquireSRWLockExclusive(&state->lock)) { oiv1_unlock(); receipt->status=OIV1_STATUS_BUSY; return NULL; }
            InterlockedIncrement(&core->interactive_refs); InterlockedIncrement(&adapter->interactive_refs);
            *core_out=core; *adapter_out=adapter;
            oiv1_unlock(); return state;
        }
    }
    oiv1_unlock(); receipt->status=OIV1_STATUS_STALE; return NULL;
}
static void oiv1_put(Oiv1State* state, OwnedWinLease* core, OwnedWinV3Slot* adapter) {
    ReleaseSRWLockExclusive(&state->lock); oiv1_drop(core,adapter);
}
#ifdef SIMPLE_RUNTIME_INTERACTIVE_V1_TEST_HOOKS
int simple_owned_interactive_v1_test_input_pending(int64_t handle) {
    Oiv1Receipt receipt; oiv1_output(&receipt,sizeof(receipt)); OwnedWinLease* core; OwnedWinV3Slot* adapter;
    Oiv1State* s=oiv1_take(handle,&receipt,&core,&adapter); if (!s) return -1;
    int pending=s->input_pending; oiv1_put(s,core,adapter); return pending;
}
#endif
static void oiv1_error(Oiv1State* s, DWORD error) {
    if (!s->error_domain) { s->error_domain=OIV1_ERROR_WIN32; s->error_code=error; }
}
static void oiv1_contract_error(Oiv1State* s,uint64_t code) {
    if (!s->error_domain) { s->error_domain=OIV1_ERROR_CONTRACT; s->error_code=code; }
}
static void oiv1_ring_push(Oiv1Ring* ring, const uint8_t* bytes, uint64_t n) {
    for (uint64_t i=0;i<n;i++) ring->bytes[(ring->head+ring->count+i)%ring->capacity]=bytes[i];
    ring->count+=n; ring->seen+=n;
}
static void oiv1_ring_copy(Oiv1Ring* ring, uint8_t* bytes, uint64_t n) {
    for (uint64_t i=0;i<n;i++) bytes[i]=ring->bytes[(ring->head+i)%ring->capacity];
}
static void oiv1_ring_pop(Oiv1Ring* ring, uint64_t n) {
    ring->head=(ring->head+n)%ring->capacity; ring->count-=n;
}
static void oiv1_delivery(Oiv1State* s) {
    uint64_t intent=(uint64_t)InterlockedCompareExchange64(&owned_win_leases[s->core_index].interactive_intent,0,0);
    LONG decision=(LONG)(intent&3);
    if (!s->ticket_kind || !decision) return;
    if (s->ticket_kind==1) InterlockedExchange(&s->start_decision,decision);
    if (s->ticket_kind==2 && decision==1) {
        oiv1_ring_pop(&s->output,s->delivery_out); oiv1_ring_pop(&s->error,s->delivery_err);
        s->output.delivered+=s->delivery_out; s->error.delivered+=s->delivery_err;
    }
    s->ticket_kind=0; s->delivery_out=s->delivery_err=0;
    /* Preserve sequence, seal and final decision for duplicate resolutions. */
}
static void oiv1_snapshot(Oiv1State* s,Oiv1Receipt* r) {
    oiv1_delivery(s);
    r->status=OIV1_STATUS_OK; r->handle_echo=(int64_t)s->handle;
    r->validity_mask=OIV1_VALID_OWNER|OIV1_VALID_PHASE|OIV1_VALID_INPUT|
        OIV1_VALID_STREAMS|OIV1_VALID_EXIT|OIV1_VALID_COUNTS|OIV1_VALID_ERROR;
    r->phase=s->phase; r->stdin_state=s->stdin_state;
    r->stdout_state=s->output.state; r->stderr_state=s->error.state;
    r->exit_kind=s->exit_kind; r->exit_value=(int64_t)s->exit_value;
    r->error_domain=s->error_domain; r->error_code=s->error_code;
    r->accepted_total=s->accepted; r->written_total=s->written;
    r->stdin_queued=s->input.count; r->stdout_seen_total=s->output.seen;
    r->stderr_seen_total=s->error.seen; r->stdout_delivered_total=s->output.delivered;
    r->stderr_delivered_total=s->error.delivered;
    r->stdout_discarded_total=s->output.discarded; r->stderr_discarded_total=s->error.discarded;
    r->flags=s->flags|OIV1_FLAG_OWNERHELD; r->operation_sequence=s->sequence;
    if (s->input_progress_uncertain) r->validity_mask&=~(OIV1_VALID_INPUT|OIV1_VALID_COUNTS);
    if (s->error_domain) r->status=OIV1_STATUS_NATIVEFAILURE;
    if (s->flags&OIV1_FLAG_TIMEDOUT) r->status=OIV1_STATUS_DEADLINEREACHED;
}
static void oiv1_ticket(Oiv1State* s,Oiv1Receipt* r,uint64_t kind) {
    s->ticket_kind=kind; s->ticket_sequence=++s->sequence;
    /* generation and seal are CSPRNG-derived, never raw addresses. */
    r->ticket0=s->core_index; r->ticket1=s->generation;
    r->ticket2=s->ticket_sequence; r->ticket3=s->ticket_seal;
    r->flags|=OIV1_FLAG_LOANPRESENT;
    InterlockedExchange(&s->delivery_decision,0);
    InterlockedExchange64(&owned_win_leases[s->core_index].interactive_intent,
        (LONG64)((s->generation<<32)|(s->ticket_sequence<<2)));
}
static int oiv1_pipe(Oiv1State* s,Oiv1Ring* ring,int input) {
    WCHAR name[160];
    _snwprintf(name,160,L"\\\\.\\pipe\\simple-interactive-%lu-%llu-%u-%u",
        GetCurrentProcessId(),(unsigned long long)s->generation,s->core_index,
        input?0:(ring==&s->output?1:2));
    SECURITY_ATTRIBUTES security={sizeof(security),NULL,TRUE};
    DWORD access=(input?PIPE_ACCESS_OUTBOUND:PIPE_ACCESS_INBOUND)|FILE_FLAG_OVERLAPPED|FILE_FLAG_FIRST_PIPE_INSTANCE;
    ring->parent=CreateNamedPipeW(name,access,PIPE_TYPE_BYTE|PIPE_READMODE_BYTE|PIPE_WAIT,
        1,65536,65536,0,NULL);
    if (ring->parent==INVALID_HANDLE_VALUE) { ring->parent=NULL; return 0; }
    ring->child=CreateFileW(name,input?GENERIC_READ:GENERIC_WRITE,0,&security,OPEN_EXISTING,0,NULL);
    if (ring->child==INVALID_HANDLE_VALUE) { ring->child=NULL; return 0; }
    /* Client open establishes the connection before an overlapped server call. */
    ring->io.hEvent=CreateEventW(NULL,TRUE,FALSE,NULL);
    return ring->io.hEvent!=NULL;
}
static int oiv1_spawn(Oiv1State* s) {
    if (!oiv1_pipe(s,&s->input,1) || !oiv1_pipe(s,&s->output,0) || !oiv1_pipe(s,&s->error,0)) return 0;
    s->job=CreateJobObjectW(NULL,NULL);
    JOBOBJECT_EXTENDED_LIMIT_INFORMATION limit; memset(&limit,0,sizeof(limit));
    limit.BasicLimitInformation.LimitFlags=JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
    if (!s->job || !SetInformationJobObject(s->job,JobObjectExtendedLimitInformation,&limit,sizeof(limit))) return 0;
    SIZE_T bytes=0; InitializeProcThreadAttributeList(NULL,2,0,&bytes);
    LPPROC_THREAD_ATTRIBUTE_LIST attrs=(LPPROC_THREAD_ATTRIBUTE_LIST)malloc(bytes);
    if (!attrs) { SetLastError(ERROR_NOT_ENOUGH_MEMORY); return 0; }
    int initialized=InitializeProcThreadAttributeList(attrs,2,0,&bytes)!=0;
    HANDLE inherit[]={s->input.child,s->output.child,s->error.child};
    int ready=initialized && UpdateProcThreadAttribute(attrs,0,PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
        inherit,sizeof(inherit),NULL,NULL) && UpdateProcThreadAttribute(attrs,0,PROC_THREAD_ATTRIBUTE_JOB_LIST,
        &s->job,sizeof(s->job),NULL,NULL);
    STARTUPINFOEXW startup; memset(&startup,0,sizeof(startup));
    startup.StartupInfo.cb=sizeof(startup); startup.StartupInfo.dwFlags=STARTF_USESTDHANDLES;
    startup.StartupInfo.hStdInput=s->input.child; startup.StartupInfo.hStdOutput=s->output.child;
    startup.StartupInfo.hStdError=s->error.child; startup.lpAttributeList=attrs;
    PROCESS_INFORMATION child; memset(&child,0,sizeof(child));
    int ok=0;
    if (ready) {
        if (oiv1_expired(s->startup)) s->startup_refusal=1;
        else if (InterlockedCompareExchange(&s->worker_cancel,0,0)) s->startup_refusal=2;
        else ok=CreateProcessW(s->application,s->commandline,NULL,NULL,TRUE,
            EXTENDED_STARTUPINFO_PRESENT|CREATE_NO_WINDOW|CREATE_SUSPENDED,NULL,NULL,&startup.StartupInfo,&child);
    }
    DWORD error=GetLastError();
    if (initialized) DeleteProcThreadAttributeList(attrs); free(attrs);
    owned_win_close(&s->input.child); owned_win_close(&s->output.child); owned_win_close(&s->error.child);
    if (!ok) { SetLastError(error); return 0; }
    s->process=child.hProcess; s->thread=child.hThread;
#ifdef SIMPLE_RUNTIME_INTERACTIVE_V1_TEST_HOOKS
    if (oiv1_test_created_entered && oiv1_test_created_release) {
        SetEvent(oiv1_test_created_entered); WaitForSingleObject(oiv1_test_created_release,INFINITE);
    }
#endif
    return 1;
}
static void oiv1_output_complete(Oiv1State* s,Oiv1Ring* ring,DWORD n,int success,DWORD error) {
    if (n>ring->requested || n>ring->capacity-ring->count || n>INT64_MAX-ring->seen) {
        oiv1_contract_error(s,3); ring->state=OIV1_STREAM_FAILED;
    } else {
        if (n) oiv1_ring_push(ring,ring->pending_bytes,n);
        if (!success) {
            ring->state=error==ERROR_BROKEN_PIPE?OIV1_STREAM_EOF:OIV1_STREAM_FAILED;
            if (error!=ERROR_BROKEN_PIPE) oiv1_error(s,error);
        }
    }
    ring->pending=0;
}
static void oiv1_read(Oiv1State* s,Oiv1Ring* ring) {
    if (!ring->parent || ring->state!=OIV1_STREAM_OPEN) return;
    DWORD n=0;
    if (ring->pending) {
        if (GetOverlappedResult(ring->parent,&ring->io,&n,FALSE)) oiv1_output_complete(s,ring,n,1,0);
        else if (GetLastError()==ERROR_IO_INCOMPLETE) return;
        else oiv1_output_complete(s,ring,n,0,GetLastError());
        return;
    }
    uint64_t free_bytes=ring->capacity-ring->count;
    if (!free_bytes) return;
    if (ring->seen>=INT64_MAX) { oiv1_contract_error(s,4); ring->state=OIV1_STREAM_FAILED; return; }
    if (free_bytes>INT64_MAX-ring->seen) free_bytes=INT64_MAX-ring->seen;
    ring->requested=(DWORD)(free_bytes<4096?free_bytes:4096);
    ResetEvent(ring->io.hEvent);
    if (ReadFile(ring->parent,ring->pending_bytes,ring->requested,&n,&ring->io)) {
        oiv1_output_complete(s,ring,n,1,0); /* zero bytes alone is not pipe EOF */
    } else {
        DWORD error=GetLastError();
        if (error==ERROR_IO_PENDING) ring->pending=1;
        else oiv1_output_complete(s,ring,n,0,error);
    }
}
static void oiv1_input_complete(Oiv1State* s,DWORD n,int success,DWORD error) {
    if (n>s->input_requested || n>s->input.count || !s->segment_count ||
        n>s->segments[s->segment_head].count) {
        s->input_progress_uncertain=1; s->stdin_state=OIV1_STREAM_FAILED; oiv1_contract_error(s,3);
    } else {
        /* Apply reported progress exactly once, BEFORE clearing pending state. */
        oiv1_ring_pop(&s->input,n); s->written+=n;
        s->segments[s->segment_head].count-=n;
        if (!s->segments[s->segment_head].count) { s->segment_head=(s->segment_head+1)%256; s->segment_count--; }
        if (!success) {
            /* A failed/canceled write may have reached the peer beyond the
             * last OS-reported count. Retain the confirmed lower bound and
             * remove Input/Counts validity rather than claiming exact zero. */
            s->input_progress_uncertain=1; s->stdin_state=OIV1_STREAM_FAILED; oiv1_error(s,error);
        }
    }
    s->input_pending=0; s->input_requested=0;
}
static void oiv1_write(Oiv1State* s) {
    Oiv1Ring* ring=&s->input; DWORD n=0;
    if (s->input_pending) {
        if (s->segment_count && (uint64_t)s->segments[s->segment_head].expires_ms<=GetTickCount64()) {
            s->flags|=OIV1_FLAG_EXPIREDSEGMENT; s->stdin_state=OIV1_STREAM_FAILED;
            (void)CancelIoEx(ring->parent,&ring->io);
        }
        if (GetOverlappedResult(ring->parent,&ring->io,&n,FALSE)) {
            oiv1_input_complete(s,n,1,0);
        } else if (GetLastError()!=ERROR_IO_INCOMPLETE) {
            oiv1_input_complete(s,n,0,GetLastError());
        }
        return;
    }
    if (!ring->count) {
        if (s->finish_requested && ring->parent) { owned_win_close(&ring->parent); s->stdin_state=OIV1_STREAM_EOF; }
        return;
    }
    if (s->stdin_state==OIV1_STREAM_FAILED || s->cancel_requested) return;
    Oiv1Segment* segment=&s->segments[s->segment_head];
    if ((uint64_t)segment->expires_ms<=GetTickCount64()) {
        s->flags|=OIV1_FLAG_EXPIREDSEGMENT; s->stdin_state=OIV1_STREAM_FAILED; return;
    }
    DWORD count=(DWORD)(segment->count<4096?segment->count:4096);
    s->input_requested=count;
    oiv1_ring_copy(ring,ring->pending_bytes,count);
    ResetEvent(ring->io.hEvent);
    if (WriteFile(ring->parent,ring->pending_bytes,count,&n,&ring->io)) {
        oiv1_input_complete(s,n,1,0);
    } else if (GetLastError()==ERROR_IO_PENDING) s->input_pending=1;
    else oiv1_input_complete(s,n,0,GetLastError());
}
static int oiv1_io_quiet(Oiv1State* s) {
    Oiv1Ring* rings[]={&s->input,&s->output,&s->error}; int quiet=1;
    for (int i=0;i<3;i++) {
        Oiv1Ring* r=rings[i]; int pending=i==0?s->input_pending:r->pending;
        if (pending && r->parent) {
            CancelIoEx(r->parent,&r->io); DWORD n=0;
            int completed=GetOverlappedResult(r->parent,&r->io,&n,FALSE)!=0;
            DWORD error=completed?0:GetLastError();
            if (!completed && error==ERROR_IO_INCOMPLETE) { quiet=0; continue; }
            if (i==0) oiv1_input_complete(s,n,completed,error);
            else oiv1_output_complete(s,r,n,completed,error);
        }
    }
    return quiet;
}
static void oiv1_close_resources(Oiv1State* s) {
    Oiv1Ring* rings[]={&s->input,&s->output,&s->error};
    for (int i=0;i<3;i++) { owned_win_close(&rings[i]->parent); owned_win_close(&rings[i]->child); owned_win_close(&rings[i]->io.hEvent); }
    owned_win_close(&s->thread); owned_win_close(&s->process); owned_win_close(&s->job);
    s->flags|=OIV1_FLAG_RESOURCESCLOSED;
}
static DWORD WINAPI oiv1_worker(void* opaque) {
    Oiv1State* s=(Oiv1State*)opaque;
    int abandoned_start=0;
    uint64_t decision=0;
    while (!decision) {
        decision=(uint64_t)InterlockedCompareExchange(&s->start_decision,0,0);
        uint64_t key=(uint64_t)InterlockedCompareExchange64(&owned_win_leases[s->core_index].interactive_intent,0,0);
        if (!decision && ((key>>2)&UINT64_C(0x3fffffff))==1) decision=key&3;
        if (!decision) WaitForSingleObject(s->wake,INFINITE);
    }
    if (decision==2) {
        abandoned_start=1;
        AcquireSRWLockExclusive(&s->lock); s->phase=OIV1_PHASE_COLLECTED;
        s->output.state=s->error.state=s->stdin_state=OIV1_STREAM_NOTCREATED;
        s->flags|=OIV1_FLAG_NOCHILDPROVEN|OIV1_FLAG_RESOURCESCLOSED;
        ReleaseSRWLockExclusive(&s->lock); goto done;
    }
    /* All process creation is outside registry locks and outside foreground. */
    int spawned=oiv1_spawn(s); DWORD startup_error=GetLastError();
    AcquireSRWLockExclusive(&s->lock);
    if (!spawned) {
        if (s->startup_refusal) {
            s->error_domain=OIV1_ERROR_CONTRACT; s->error_code=(uint64_t)s->startup_refusal;
            if (s->startup_refusal==1) s->flags|=OIV1_FLAG_TIMEDOUT;
        } else oiv1_error(s,startup_error);
        s->flags|=OIV1_FLAG_NOCHILDPROVEN;
        s->output.state=s->error.state=s->stdin_state=OIV1_STREAM_NOTCREATED;
        s->phase=OIV1_PHASE_FAILEDHELD; oiv1_close_resources(s);
    } else {
        s->phase=OIV1_PHASE_RUNNING; s->output.state=s->error.state=s->stdin_state=OIV1_STREAM_OPEN;
        if (oiv1_expired(s->startup) || InterlockedCompareExchange(&s->worker_cancel,0,0)) {
            s->cancel_requested=1; s->flags|=OIV1_FLAG_CANCELREQUESTED;
            if (oiv1_expired(s->startup)) {
                s->flags|=OIV1_FLAG_TIMEDOUT; s->error_domain=OIV1_ERROR_CONTRACT; s->error_code=1;
            }
            s->phase=OIV1_PHASE_STOPPING;
        } else if (ResumeThread(s->thread)==(DWORD)-1) {
            oiv1_error(s,GetLastError()); s->cancel_requested=1; s->flags|=OIV1_FLAG_CANCELREQUESTED;
            s->phase=OIV1_PHASE_STOPPING;
        }
        owned_win_close(&s->thread);
    }
    ReleaseSRWLockExclusive(&s->lock);
    for (;;) {
        AcquireSRWLockExclusive(&s->lock); oiv1_delivery(s);
        if (s->cancel_requested && s->job && !s->kill_sent) {
            if (!TerminateJobObject(s->job,1)) oiv1_error(s,GetLastError()); else s->kill_sent=1;
            s->phase=OIV1_PHASE_STOPPING;
        }
        if (spawned && s->cancel_requested && !s->input_pending) s->stdin_state=OIV1_STREAM_FAILED;
        if (spawned) {
            oiv1_write(s); oiv1_read(s,&s->output); oiv1_read(s,&s->error);
            DWORD waited=WaitForSingleObject(s->process,0);
            if (waited==WAIT_OBJECT_0 && !s->exit_kind) {
                DWORD code=0;
                if (GetExitCodeProcess(s->process,&code)) { s->exit_kind=OIV1_EXIT_EXITED; s->exit_value=code; s->flags|=OIV1_FLAG_REAPED; }
                else oiv1_error(s,GetLastError());
            } else if (waited==WAIT_FAILED) oiv1_error(s,GetLastError());
            JOBOBJECT_BASIC_ACCOUNTING_INFORMATION info; memset(&info,0,sizeof(info));
            if (QueryInformationJobObject(s->job,JobObjectBasicAccountingInformation,&info,sizeof(info),NULL)) {
                if (!info.ActiveProcesses) s->flags|=OIV1_FLAG_TREEEMPTY;
            } else oiv1_error(s,GetLastError());
            if (s->exit_kind && (s->flags&OIV1_FLAG_TREEEMPTY) &&
                s->output.state!=OIV1_STREAM_OPEN && s->error.state!=OIV1_STREAM_OPEN) s->phase=OIV1_PHASE_TERMINAL;
        }
        if (s->collect_requested && !s->ticket_kind) {
            if (s->discard) {
                s->output.discarded+=s->output.count; oiv1_ring_pop(&s->output,s->output.count);
                s->error.discarded+=s->error.count; oiv1_ring_pop(&s->error,s->error.count);
            }
            if ((s->phase==OIV1_PHASE_TERMINAL || s->phase==OIV1_PHASE_FAILEDHELD) &&
                !s->output.count && !s->error.count && oiv1_io_quiet(s) && !s->output.count && !s->error.count) {
                oiv1_close_resources(s); s->phase=OIV1_PHASE_COLLECTED;
                ReleaseSRWLockExclusive(&s->lock); break;
            }
        }
        HANDLE events[5]; DWORD count=0; events[count++]=s->wake;
        if (spawned && !s->exit_kind) events[count++]=s->process;
        if (s->input_pending) events[count++]=s->input.io.hEvent;
        if (s->output.pending) events[count++]=s->output.io.hEvent;
        if (s->error.pending) events[count++]=s->error.io.hEvent;
        DWORD wait=INFINITE;
        if ((s->output.state==OIV1_STREAM_OPEN && !s->output.pending && s->output.count<s->output.capacity) ||
            (s->error.state==OIV1_STREAM_OPEN && !s->error.pending && s->error.count<s->error.capacity) ||
            (s->input.count && !s->input_pending && s->stdin_state==OIV1_STREAM_OPEN && !s->cancel_requested) ||
            (s->finish_requested && !s->input.count && s->input.parent)) wait=0;
        if (s->segment_count && s->stdin_state==OIV1_STREAM_OPEN) {
            uint64_t now=GetTickCount64(),expires=(uint64_t)s->segments[s->segment_head].expires_ms;
            DWORD until=expires>now?(DWORD)(expires-now):0; if (until<wait) wait=until;
        }
        /* Windows Job handles are not waitable. After leader exit only, a
         * bounded timer samples descendant finality; resident idle is event-only. */
        if ((s->exit_kind && !(s->flags&OIV1_FLAG_TREEEMPTY)) || (spawned && s->cancel_requested && !s->kill_sent))
            if (wait>250) wait=250;
        ReleaseSRWLockExclusive(&s->lock);
        WaitForMultipleObjects(count,events,FALSE,wait);
    }
done:;
    /* These atomic pins were acquired before submission; no global lock on exit. */
    uint64_t final_handle=s->handle;
    uint32_t final_core=s->core_index, final_adapter=s->adapter_index;
    InterlockedExchange(&s->worker_done,1);
    oiv1_drop(&owned_win_leases[final_core],&owned_win_v3_slots[final_adapter]);
    /* No payload access after dropping the worker pins. An aborted projection
     * has no public lease, so this SAME owner task performs deferred metadata
     * retirement. Every attempt is bounded; contention retains the entry. */
    if (abandoned_start) for (;;) {
        Oiv1ReleaseRequest release={1,sizeof(release),(int64_t)final_handle}; Oiv1Receipt receipt;
        simple_owned_interactive_v1_release(&release,sizeof(release),&receipt,sizeof(receipt));
        if (receipt.status==OIV1_STATUS_STALE || receipt.phase==OIV1_PHASE_RELEASED) break;
        WaitForSingleObject((HANDLE)InterlockedCompareExchangePointer(&owned_win_leases[final_core].interactive_wake,NULL,NULL),250);
    }
    return 0;
}

int64_t simple_owned_interactive_v1_capabilities(Oiv1Capabilities* out,uint64_t size) {
    if (!out || size!=sizeof(*out)) return -1;
    memset(out,0,sizeof(*out)); out->version=1; out->size=sizeof(*out);
    out->capability_mask=OIV1_CAP_REQUIRED; out->max_leases=128;
    out->stdin_capacity_max=65536; out->stdout_capacity_max=out->stderr_capacity_max=262144;
    out->write_quantum=4096; out->output_chunk_max=65536; out->poll_wait_max=250;
    out->segment_max=256; out->clock_tag=1; return 0;
}
int64_t simple_owned_interactive_v1_deadline(const Oiv1DeadlineRequest* req,uint64_t size,
                                           Oiv1Deadline* d,Oiv1Receipt* r,uint64_t out_size) {
    if (!oiv1_output(r,out_size) || !d) return -1;
    memset(d,0,sizeof(*d));
    if (!oiv1_request(req,size,sizeof(*req)) || req->timeout_ms>600000) return oiv1_invalid(r);
    d->version=1; d->size=sizeof(*d); d->clock_tag=1; d->expires_ms=(int64_t)(GetTickCount64()+req->timeout_ms); return 0;
}

static void oiv1_free_unpublished(Oiv1State* s) {
    if (!s) return;
    if (s->argv) { for (int i=0;s->argv[i];i++) free(s->argv[i]); free(s->argv); }
    RT_OWNED_HOST_FREE(s->application); RT_OWNED_HOST_FREE(s->commandline);
    if (!s->wake_registered) owned_win_close(&s->wake);
    owned_win_close(&s->unused_wake);
    free(s->input.bytes); free(s->output.bytes); free(s->error.bytes); free(s);
}
static int oiv1_text_span(Oiv1ConstSpan span) {
    return span.len<=32768 && (!span.len || span.data) &&
        (!span.len || !memchr(span.data,0,(size_t)span.len)) &&
        (!span.len || MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,(const char*)span.data,(int)span.len,NULL,0)>0);
}
int64_t simple_owned_interactive_v1_start_begin(const Oiv1StartRequest* req,uint64_t size,Oiv1Receipt* r,uint64_t out_size) {
    if (!oiv1_output(r,out_size)) return -1;
    if (!oiv1_request(req,size,sizeof(*req)) || req->deadline.version!=1 || req->deadline.size!=sizeof(Oiv1Deadline) ||
        req->deadline.clock_tag!=1 || req->deadline.expires_ms<0 ||
        (uint64_t)req->deadline.expires_ms>GetTickCount64()+600000 || req->flags || !req->stdin_capacity || req->stdin_capacity>65536 ||
        !req->stdout_capacity || req->stdout_capacity>262144 || !req->stderr_capacity || req->stderr_capacity>262144 ||
        !oiv1_text_span(req->command) || !req->command.len || req->args.count>128 ||
        (req->args.count && !req->args.data)) return oiv1_invalid(r);
    if (oiv1_expired(req->deadline)) { r->status=OIV1_STATUS_DEADLINEREACHED; return 0; }
    Oiv1State* s=(Oiv1State*)calloc(1,sizeof(*s));
    if (!s) { r->status=OIV1_STATUS_PROJECTIONFAILURE; return 0; }
    /* Unpublished state: exactly one owner, so one nonblocking attempt wins. */
    if (!TryAcquireSRWLockExclusive(&s->lock)) { free(s); r->status=OIV1_STATUS_BUSY; return 0; }
    s->wake=CreateEventW(NULL,FALSE,FALSE,NULL);
    if (!s->wake) goto allocation_failed;
    s->argv=(char**)calloc((size_t)req->args.count+2,sizeof(char*));
    s->input.capacity=req->stdin_capacity; s->output.capacity=req->stdout_capacity; s->error.capacity=req->stderr_capacity;
    s->input.bytes=(uint8_t*)malloc((size_t)s->input.capacity);
    s->output.bytes=(uint8_t*)malloc((size_t)s->output.capacity); s->error.bytes=(uint8_t*)malloc((size_t)s->error.capacity);
    uint64_t total=req->command.len;
    if (!s->argv || !s->input.bytes || !s->output.bytes || !s->error.bytes) goto allocation_failed;
    for (uint64_t i=0;i<=req->args.count;i++) {
        Oiv1ConstSpan text=i?req->args.data[i-1]:req->command;
        if (!oiv1_text_span(text) || (i && text.len>32768-total)) { oiv1_free_unpublished(s); return oiv1_invalid(r); }
        if (i) total+=text.len;
        s->argv[i]=(char*)malloc((size_t)text.len+1); if (!s->argv[i]) goto allocation_failed;
        if (text.len) memcpy(s->argv[i],text.data,(size_t)text.len);
        s->argv[i][text.len]=0;
    }
    /* Require a fully absolute path, never PATH search or shell parsing. */
    if (!(req->command.len>=3 && ((s->argv[0][1]==':' && (s->argv[0][2]=='\\' || s->argv[0][2]=='/')) ||
        (s->argv[0][0]=='\\' && s->argv[0][1]=='\\')))) { oiv1_free_unpublished(s); return oiv1_invalid(r); }
    s->application=owned_win_widen(s->argv[0]);
    char* command=owned_win_build_cmdline((const char* const*)s->argv);
    if (command) { s->commandline=owned_win_widen(command); RT_OWNED_HOST_FREE(command); }
    if (!s->application || !s->commandline) goto allocation_failed;
    RtOwnedProcessTokenV2 entropy; memset(&entropy,0,sizeof(entropy));
    if (!owned_win_random_token(&entropy)) goto allocation_failed;
    if (!oiv1_locks(r)) { oiv1_free_unpublished(s); return 0; }
    uint32_t c=128,a=128;
    for (uint32_t i=0;i<128;i++) { if (!owned_win_leases[i].used && c==128) c=i;
        if (!owned_win_v3_slots[i].active && a==128) a=i; }
    uint64_t handle=entropy.low&UINT64_C(0x0fffffffffffffff);
    for (uint32_t i=0;i<128;i++) if (owned_win_v3_slots[i].active && owned_win_v3_slots[i].handle==handle) handle=0;
    if (c==128 || a==128 || !handle || !entropy.high || oiv1_expired(req->deadline)) {
        oiv1_unlock(); oiv1_free_unpublished(s); r->status=OIV1_STATUS_REJECTEDBEFORESTART;
        r->flags=OIV1_FLAG_NOCHILDPROVEN; return 0;
    }
    OwnedWinLease* core=&owned_win_leases[c]; OwnedWinV3Slot* adapter=&owned_win_v3_slots[a];
    if (InterlockedCompareExchange(&core->interactive_gate,1,0)!=0) {
        oiv1_unlock(); oiv1_free_unpublished(s); r->status=OIV1_STATUS_BUSY; return 0;
    }
    /* Free slots only: preserve the permanent atomic gate while initializing. */
    uint64_t epoch=(uint64_t)InterlockedCompareExchange64(&core->interactive_epoch,0,0);
    if (epoch>=UINT64_C(0xffffffff)) {
        InterlockedExchange(&core->interactive_gate,0); oiv1_unlock(); oiv1_free_unpublished(s);
        r->status=OIV1_STATUS_REJECTEDBEFORESTART; r->flags=OIV1_FLAG_NOCHILDPROVEN; return 0;
    }
    epoch++; InterlockedExchange64(&core->interactive_epoch,(LONG64)epoch);
    InterlockedExchange64(&core->interactive_seal,(LONG64)entropy.low);
    core->used=3; core->token=entropy; core->interactive_generation=epoch;
    core->interactive_state=s; core->interactive_refs=1;
    HANDLE permanent=(HANDLE)InterlockedCompareExchangePointer(&core->interactive_wake,s->wake,NULL);
    if (permanent) { s->unused_wake=s->wake; s->wake=permanent; }
    s->wake_registered=1;
    adapter->active=1; adapter->published=1; adapter->handle=handle; adapter->token=entropy;
    adapter->interactive_mode=1; adapter->interactive_refs=1;
    s->core_index=c; s->adapter_index=a; s->handle=handle; s->generation=epoch;
    s->ticket_seal=entropy.low; s->startup=req->deadline; s->phase=OIV1_PHASE_STARTING;
    s->flags=OIV1_FLAG_OWNERHELD|OIV1_FLAG_STARTPUBLICATIONPENDING;
    oiv1_snapshot(s,r); oiv1_ticket(s,r,1);
    InterlockedExchange(&core->interactive_gate,0); oiv1_unlock();
    /* Worker may prepare but cannot attempt child creation until COMMIT. */
    int submitted=0;
#ifdef SIMPLE_RUNTIME_INTERACTIVE_V1_TEST_HOOKS
    if (InterlockedCompareExchange(&oiv1_test_submit_failures,0,0)>0 &&
        InterlockedDecrement(&oiv1_test_submit_failures)>=0) SetLastError(ERROR_NOT_ENOUGH_MEMORY);
    else
#endif
    submitted=QueueUserWorkItem(oiv1_worker,s,WT_EXECUTELONGFUNCTION)!=0;
    if (!submitted) {
        oiv1_error(s,GetLastError()); s->phase=OIV1_PHASE_FAILEDHELD;
        s->flags|=OIV1_FLAG_NOCHILDPROVEN|OIV1_FLAG_RESOURCESCLOSED;
        s->output.state=s->error.state=s->stdin_state=OIV1_STREAM_NOTCREATED;
        oiv1_snapshot(s,r); r->flags|=OIV1_FLAG_LOANPRESENT;
        InterlockedExchange(&s->worker_done,1); oiv1_drop(core,adapter);
    }
    owned_win_close(&s->unused_wake);
    ReleaseSRWLockExclusive(&s->lock);
    return 0;
allocation_failed:
    oiv1_free_unpublished(s); r->status=OIV1_STATUS_PROJECTIONFAILURE; return 0;
}

int64_t simple_owned_interactive_v1_resolve(const Oiv1ResolveRequest* req,uint64_t size) {
    if (!oiv1_request(req,size,sizeof(*req)) || (req->action!=1 && req->action!=2) ||
        req->ticket.word0>=128 || !req->ticket.word1 || req->ticket.word1>UINT64_C(0xffffffff) ||
        !req->ticket.word2 || req->ticket.word2>UINT64_C(0x3fffffff)) return -1;
    OwnedWinLease* slot=&owned_win_leases[req->ticket.word0];
    /* Permanent fields only, including on stale/recycled tickets. The CAS key
     * contains the NEVER-reused epoch+sequence, so separate seal reads cannot
     * authorize a new generation. Refuse exhaustion instead of wrapping. */
    uint64_t seal=(uint64_t)InterlockedCompareExchange64(&slot->interactive_seal,0,0);
    if (seal!=req->ticket.word3) return OIV1_RESOLVE_STALE;
    uint64_t key=(req->ticket.word1<<32)|(req->ticket.word2<<2);
    uint64_t actual=(uint64_t)InterlockedCompareExchange64(&slot->interactive_intent,
        (LONG64)(key|req->action),(LONG64)key);
    if (actual==key) {
        HANDLE wake=(HANDLE)InterlockedCompareExchangePointer(&slot->interactive_wake,NULL,NULL);
        if (wake) SetEvent(wake); /* permanent registry infrastructure, never recycled */
        return OIV1_RESOLVE_RECORDED;
    }
    if ((actual&~UINT64_C(3))!=key) return OIV1_RESOLVE_STALE;
    return (actual&3)==req->action?OIV1_RESOLVE_ALREADYSAME:OIV1_RESOLVE_CONFLICTING;
}

static int oiv1_deadline_valid(Oiv1Deadline d) {
    return d.version==1 && d.size==sizeof(d) && d.clock_tag==1 && d.expires_ms>=0 &&
        (uint64_t)d.expires_ms<=GetTickCount64()+600000;
}
int64_t simple_owned_interactive_v1_write_some(const Oiv1WriteRequest* req,uint64_t size,Oiv1Receipt* r,uint64_t out_size) {
    if (!oiv1_output(r,out_size)) return -1;
    if (!oiv1_request(req,size,sizeof(*req)) || !oiv1_deadline_valid(req->deadline) ||
        req->max_bytes>4096 || req->data_offset>req->bytes.len ||
        (req->bytes.len && !req->bytes.data)) return oiv1_invalid(r);
    if (oiv1_expired(req->deadline)) { r->status=OIV1_STATUS_DEADLINEREACHED; return 0; }
    OwnedWinLease* core; OwnedWinV3Slot* adapter;
    Oiv1State* s=oiv1_take(req->handle,r,&core,&adapter); if (!s) return 0;
    oiv1_snapshot(s,r);
    if (oiv1_expired(req->deadline)) r->status=OIV1_STATUS_DEADLINEREACHED;
    else if (s->accepted!=req->expected_accepted_total) r->status=OIV1_STATUS_CONFLICT;
    else if (s->phase==OIV1_PHASE_STARTING) r->status=OIV1_STATUS_PENDING;
    else if (s->phase!=OIV1_PHASE_RUNNING || s->cancel_requested || s->finish_requested || s->stdin_state!=OIV1_STREAM_OPEN ||
        (s->flags&OIV1_FLAG_EXPIREDSEGMENT)) r->status=OIV1_STATUS_NOTREADY;
    else if (s->segment_count==256) r->status=OIV1_STATUS_PENDING;
    else {
        uint64_t n=req->bytes.len-req->data_offset;
        if (n>req->max_bytes) n=req->max_bytes;
        if (n>s->input.capacity-s->input.count) n=s->input.capacity-s->input.count;
        if (n>INT64_MAX-s->accepted) { r->status=OIV1_STATUS_NOTREADY; }
        else if (n) {
            oiv1_ring_push(&s->input,req->bytes.data+req->data_offset,n);
            uint32_t segment=(s->segment_head+s->segment_count)%256;
            s->segments[segment].count=n; s->segments[segment].expires_ms=req->deadline.expires_ms;
            s->segment_count++; s->accepted+=n; SetEvent(s->wake); oiv1_snapshot(s,r); r->accepted_delta=n;
        } else r->status=OIV1_STATUS_PENDING;
    }
    oiv1_put(s,core,adapter); return 0;
}

int64_t simple_owned_interactive_v1_poll_begin(const Oiv1PollRequest* req,uint64_t size,Oiv1Receipt* r,uint64_t out_size) {
    if (!oiv1_output(r,out_size)) return -1;
    if (!oiv1_request(req,size,sizeof(*req)) || !oiv1_deadline_valid(req->deadline) || req->wait_ms>250 ||
        req->stdout_buffer.capacity>65536 || req->stderr_buffer.capacity>65536 ||
        (req->stdout_buffer.capacity && !req->stdout_buffer.data) ||
        (req->stderr_buffer.capacity && !req->stderr_buffer.data)) return oiv1_invalid(r);
    if (oiv1_expired(req->deadline)) { r->status=OIV1_STATUS_DEADLINEREACHED; return 0; }
    OwnedWinLease* core; OwnedWinV3Slot* adapter;
    Oiv1State* s=oiv1_take(req->handle,r,&core,&adapter); if (!s) return 0;
    oiv1_snapshot(s,r);
    if (req->wait_ms && !s->output.count && !s->error.count && s->phase<OIV1_PHASE_TERMINAL) {
        uint64_t now=GetTickCount64(),remaining=(uint64_t)req->deadline.expires_ms>now?(uint64_t)req->deadline.expires_ms-now:0;
        DWORD wait=(DWORD)(remaining<req->wait_ms?remaining:req->wait_ms);
        r->status=OIV1_STATUS_PENDING; r->flags|=OIV1_FLAG_OBSERVEDBEFOREWAIT;
        ReleaseSRWLockExclusive(&s->lock);
        /* No global/private lock held; pins retain stable owner storage. */
        if (wait) Sleep(wait);
#ifdef SIMPLE_RUNTIME_INTERACTIVE_V1_TEST_HOOKS
        if (oiv1_test_poll_wait_entered && oiv1_test_poll_wait_release) {
            SetEvent(oiv1_test_poll_wait_entered); WaitForSingleObject(oiv1_test_poll_wait_release,INFINITE);
        }
#endif
        Oiv1Receipt fresh; oiv1_output(&fresh,sizeof(fresh));
        OwnedWinLease* next_core; OwnedWinV3Slot* next_adapter;
        Oiv1State* next=oiv1_take(req->handle,&fresh,&next_core,&next_adapter);
        oiv1_drop(core,adapter);
        if (!next) { r->flags|=OIV1_FLAG_MAINTENANCEDEFERRED;
            if (oiv1_expired(req->deadline)) r->status=OIV1_STATUS_DEADLINEREACHED; return 0; }
        if (oiv1_expired(req->deadline)) {
            r->status=OIV1_STATUS_DEADLINEREACHED; oiv1_put(next,next_core,next_adapter); return 0;
        }
        s=next; core=next_core; adapter=next_adapter; oiv1_snapshot(s,r);
    }
    if (oiv1_expired(req->deadline)) {
        r->status=OIV1_STATUS_DEADLINEREACHED;
        oiv1_put(s,core,adapter); return 0;
    }
    if (s->ticket_kind) { r->status=OIV1_STATUS_PENDING; oiv1_put(s,core,adapter); return 0; }
    uint64_t out=s->output.count<req->stdout_buffer.capacity?s->output.count:req->stdout_buffer.capacity;
    uint64_t err=s->error.count<req->stderr_buffer.capacity?s->error.count:req->stderr_buffer.capacity;
    if (out || err) {
        if (s->sequence>=UINT64_C(0x3fffffff)) { r->status=OIV1_STATUS_NOTREADY; oiv1_put(s,core,adapter); return 0; }
        oiv1_ring_copy(&s->output,req->stdout_buffer.data,out); oiv1_ring_copy(&s->error,req->stderr_buffer.data,err);
        s->delivery_out=out; s->delivery_err=err; oiv1_ticket(s,r,2);
        r->stdout_count=out; r->stderr_count=err; r->stdout_delivered_total+=out; r->stderr_delivered_total+=err;
        r->validity_mask|=OIV1_VALID_OUTPUT; r->flags|=OIV1_FLAG_OUTPUTDELIVERYRESERVED;
    } else if (s->phase==OIV1_PHASE_STARTING || s->phase==OIV1_PHASE_RUNNING || s->phase==OIV1_PHASE_STOPPING) r->status=OIV1_STATUS_PENDING;
    oiv1_put(s,core,adapter); return 0;
}

static int64_t oiv1_control(const Oiv1ControlRequest* req,uint64_t size,Oiv1Receipt* r,uint64_t out_size,int operation) {
    if (!oiv1_output(r,out_size)) return -1;
    if (!oiv1_request(req,size,sizeof(*req)) || !oiv1_deadline_valid(req->deadline) ||
        (req->flags && (operation!=3 || req->flags!=1))) return oiv1_invalid(r);
    if (oiv1_expired(req->deadline)) { r->status=OIV1_STATUS_DEADLINEREACHED; return 0; }
    OwnedWinLease* core; OwnedWinV3Slot* adapter;
    Oiv1State* s=oiv1_take(req->handle,r,&core,&adapter); if (!s) return 0;
    oiv1_delivery(s);
    if (oiv1_expired(req->deadline)) {
        oiv1_snapshot(s,r); r->status=OIV1_STATUS_DEADLINEREACHED; oiv1_put(s,core,adapter); return 0;
    }
    if (operation==1) { s->finish_requested=1; s->flags|=OIV1_FLAG_STDINFINISHREQUESTED; }
    if (operation==2) { s->cancel_requested=1; s->flags|=OIV1_FLAG_CANCELREQUESTED;
        InterlockedExchange(&s->worker_cancel,1);
        if (s->ticket_kind) {
            uint64_t key=(s->generation<<32)|(s->ticket_sequence<<2);
            /* Recovery for a projection-invariant failure: cancellation may
             * abort its still-pending same-owner cell, never override COMMIT. */
            InterlockedCompareExchange64(&core->interactive_intent,(LONG64)(key|2),(LONG64)key);
        }
    }
    if (operation==3) { s->collect_requested=1; s->discard=req->flags!=0;
        if (s->discard) s->flags|=OIV1_FLAG_DISCARDREQUESTED;
        if (s->phase==OIV1_PHASE_FAILEDHELD && (s->flags&OIV1_FLAG_NOCHILDPROVEN) &&
            (s->flags&OIV1_FLAG_RESOURCESCLOSED) && InterlockedCompareExchange(&s->worker_done,0,0) && !s->ticket_kind)
            s->phase=OIV1_PHASE_COLLECTED;
    }
    SetEvent(s->wake);
    oiv1_snapshot(s,r);
    if (operation==3 && (s->phase!=OIV1_PHASE_COLLECTED || !InterlockedCompareExchange(&s->worker_done,0,0))) {
        r->status=OIV1_STATUS_RETAINEDCLEANUP; r->flags|=OIV1_FLAG_MAINTENANCEDEFERRED;
    }
    oiv1_put(s,core,adapter); return 0;
}
int64_t simple_owned_interactive_v1_close_stdin(const Oiv1ControlRequest* q,uint64_t n,Oiv1Receipt* r,uint64_t z) { return oiv1_control(q,n,r,z,1); }
int64_t simple_owned_interactive_v1_cancel(const Oiv1ControlRequest* q,uint64_t n,Oiv1Receipt* r,uint64_t z) { return oiv1_control(q,n,r,z,2); }
int64_t simple_owned_interactive_v1_collect(const Oiv1ControlRequest* q,uint64_t n,Oiv1Receipt* r,uint64_t z) { return oiv1_control(q,n,r,z,3); }

int64_t simple_owned_interactive_v1_release(const Oiv1ReleaseRequest* req,uint64_t size,Oiv1Receipt* r,uint64_t out_size) {
    if (!oiv1_output(r,out_size)) return -1;
    if (!oiv1_request(req,size,sizeof(*req))) return oiv1_invalid(r);
    if (!oiv1_locks(r)) return 0;
    for (uint32_t a=0;a<128;a++) {
        OwnedWinV3Slot* adapter=&owned_win_v3_slots[a];
        if (!adapter->active || !adapter->interactive_mode || adapter->handle!=(uint64_t)req->handle) continue;
        for (uint32_t c=0;c<128;c++) {
            OwnedWinLease* core=&owned_win_leases[c];
            if (core->used!=3 || core->token.high!=adapter->token.high || core->token.low!=adapter->token.low) continue;
            if (InterlockedCompareExchange(&core->interactive_gate,1,0)) { oiv1_unlock(); r->status=OIV1_STATUS_BUSY; return 0; }
            Oiv1State* s=(Oiv1State*)core->interactive_state;
            if (!TryAcquireSRWLockExclusive(&s->lock)) { InterlockedExchange(&core->interactive_gate,0); oiv1_unlock(); r->status=OIV1_STATUS_BUSY; return 0; }
            oiv1_snapshot(s,r);
            if (s->phase!=OIV1_PHASE_COLLECTED || !InterlockedCompareExchange(&s->worker_done,0,0) ||
                InterlockedCompareExchange(&core->interactive_refs,0,0) ||
                InterlockedCompareExchange(&adapter->interactive_refs,0,0) || s->ticket_kind) {
                r->status=OIV1_STATUS_NOTREADY; ReleaseSRWLockExclusive(&s->lock);
                InterlockedExchange(&core->interactive_gate,0); oiv1_unlock(); return 0;
            }
            /* Invalidate BEFORE publishing this slot as free. No resolver ever
             * touches s, and its epoch is preserved across ALL legacy resets. */
            InterlockedExchange64(&core->interactive_intent,0);
            InterlockedExchange64(&core->interactive_seal,0);
            core->interactive_state=NULL; core->used=0;
            memset(adapter,0,sizeof(*adapter));
            r->phase=OIV1_PHASE_RELEASED; r->flags&=~OIV1_FLAG_OWNERHELD;
            ReleaseSRWLockExclusive(&s->lock); InterlockedExchange(&core->interactive_gate,0);
            oiv1_unlock(); oiv1_free_unpublished(s); return 0;
        }
    }
    oiv1_unlock(); r->status=OIV1_STATUS_STALE; return 0;
}

#else
/* Other hosts have no InteractiveV1 implementation yet. This is explicit
 * Unavailable and cannot satisfy the dual-runtime or functional gate. */
#if defined(_WIN32) && defined(RT_OWNED_WIN32_ASYNC_IMPLEMENTED)
static void oiv1_legacy_unlocked_maintenance(void) { /* no Interactive owner exists */ }
#endif
int64_t simple_owned_interactive_v1_capabilities(Oiv1Capabilities* out,uint64_t size) {
    if (!out || size!=sizeof(*out)) return -1;
    memset(out,0,sizeof(*out)); out->version=1; out->size=sizeof(*out); out->status=OIV1_STATUS_UNSUPPORTED; return 0;
}
static int64_t oiv1_unavailable(Oiv1Receipt* out,uint64_t size) {
    if (!oiv1_output(out,size)) return -1; out->status=OIV1_STATUS_UNSUPPORTED; return 0;
}
int64_t simple_owned_interactive_v1_deadline(const Oiv1DeadlineRequest* q,uint64_t n,Oiv1Deadline* d,Oiv1Receipt* r,uint64_t z) {
    (void)q;(void)n; if (!d) return -1; memset(d,0,sizeof(*d)); return oiv1_unavailable(r,z);
}
#define OIV1_UNAVAILABLE(name,type) int64_t simple_owned_interactive_v1_##name(const type* q,uint64_t n,Oiv1Receipt* r,uint64_t z) { (void)q;(void)n;return oiv1_unavailable(r,z); }
OIV1_UNAVAILABLE(start_begin,Oiv1StartRequest)
OIV1_UNAVAILABLE(write_some,Oiv1WriteRequest)
OIV1_UNAVAILABLE(poll_begin,Oiv1PollRequest)
OIV1_UNAVAILABLE(close_stdin,Oiv1ControlRequest)
OIV1_UNAVAILABLE(cancel,Oiv1ControlRequest)
OIV1_UNAVAILABLE(collect,Oiv1ControlRequest)
OIV1_UNAVAILABLE(release,Oiv1ReleaseRequest)
#undef OIV1_UNAVAILABLE
int64_t simple_owned_interactive_v1_resolve(const Oiv1ResolveRequest* q,uint64_t n) { (void)q;(void)n;return OIV1_RESOLVE_STALE; }
#endif
