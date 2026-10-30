/* Portable deterministic transport test using Win32 API fakes. This exercises
 * the production input state machine; it is not native Windows evidence. */
#ifdef NDEBUG
#error "The input transport selfcheck requires active assertions"
#endif
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <wchar.h>

typedef void* HANDLE;
typedef uint32_t DWORD;
typedef wchar_t WCHAR;
typedef struct { HANDLE hEvent; } OVERLAPPED;
typedef struct { int unused; } SECURITY_ATTRIBUTES;
typedef struct { uint64_t high, low; } RtOwnedProcessTokenV2;
typedef struct {
    HANDLE input_pipe;
    OVERLAPPED input_io;
    uint8_t* input;
    uint8_t input_sha256[32];
    uint64_t input_len, input_written;
    DWORD input_requested;
    int input_contract_v3, input_pending, input_stopping, runtime_error;
} OwnedWinLease;
#define TRUE 1
#define FALSE 0
#define INVALID_HANDLE_VALUE ((HANDLE)(intptr_t)-1)
#define ERROR_BROKEN_PIPE 109
#define ERROR_NO_DATA 232
#define ERROR_OPERATION_ABORTED 995
#define ERROR_IO_INCOMPLETE 996
#define ERROR_IO_PENDING 997
#define PIPE_ACCESS_OUTBOUND 1
#define FILE_FLAG_OVERLAPPED 2
#define FILE_FLAG_FIRST_PIPE_INSTANCE 4
#define PIPE_TYPE_BYTE 0
#define PIPE_READMODE_BYTE 0
#define PIPE_WAIT 0
#define PIPE_REJECT_REMOTE_CLIENTS 8
#define GENERIC_READ 1
#define OPEN_EXISTING 3
#define RT_OWNED_HOST_MALLOC malloc
static unsigned freed, closed, writes, cancellations;
static DWORD last_error, write_error, completion_error, sync_count, completed;
static const uint8_t* write_address;
static DWORD write_count;
static void counted_free(void* p) { if (p) freed++; free(p); }
#define RT_OWNED_HOST_FREE counted_free
static void owned_win_close(HANDLE* p) { if (*p && *p != INVALID_HANDLE_VALUE) closed++; *p = NULL; }
static void owned_win_lease_error(OwnedWinLease* s, int e) { if (!s->runtime_error) s->runtime_error = e; }
static int owned_win_random_token(RtOwnedProcessTokenV2* t) { t->high = 1; t->low = 2; return 1; }
static DWORD GetLastError(void) { return last_error; }
static int CancelIoEx(HANDLE h, OVERLAPPED* o) { (void)h; (void)o; cancellations++; return 1; }
static int GetOverlappedResult(HANDLE h, OVERLAPPED* o, DWORD* n, int wait) {
    (void)h; (void)o; assert(!wait); last_error = completion_error; *n = completed; return !completion_error;
}
static int ResetEvent(HANDLE h) { assert(h); return 1; }
static int WriteFile(HANDLE h, const void* p, DWORD n, DWORD* wrote, OVERLAPPED* o) {
    assert(h && o->hEvent && n && n <= 16384); writes++;
    write_address = p; write_count = n; last_error = write_error;
    *wrote = sync_count ? sync_count : n; return !write_error;
}
static HANDLE CreateNamedPipeW(const WCHAR* name, DWORD mode, DWORD pipe_mode,
    DWORD instances, DWORD out, DWORD in, DWORD timeout, void* security) {
    assert(wcsstr(name, L"\\\\.\\pipe\\simple-owned-input-") == name);
    assert(mode == (PIPE_ACCESS_OUTBOUND | FILE_FLAG_OVERLAPPED | FILE_FLAG_FIRST_PIPE_INSTANCE));
    assert(pipe_mode == PIPE_REJECT_REMOTE_CLIENTS && instances == 1 && out == 16384 && in == 16384);
    assert(!timeout && !security); return (HANDLE)(uintptr_t)1;
}
static HANDLE CreateEventW(void* security, int manual, int signaled, void* name) {
    assert(!security && manual && !signaled && !name); return (HANDLE)(uintptr_t)2;
}
static HANDLE CreateFileW(const WCHAR* name, DWORD access, DWORD share, SECURITY_ATTRIBUTES* sa,
    DWORD disposition, DWORD flags, void* template_file) {
    (void)name; assert(access == GENERIC_READ && !share && sa && disposition == OPEN_EXISTING);
    assert(!flags && !template_file); return (HANDLE)(uintptr_t)3;
}
/* Deliberately no ConnectNamedPipe stub: successful private CreateFileW
 * establishes the connection, with no pending-connect cleanup path. */
#include "runtime_process_owned_sha256_private.h"
#include "runtime_process_owned_windows_input_private.h"

static OwnedWinLease prepare(size_t length) {
    OwnedWinLease slot = {0}; SECURITY_ATTRIBUTES security = {0}; HANDLE child = NULL;
    uint8_t* bytes = malloc(length ? length : 1); assert(bytes);
    for (size_t i = 0; i < length; i++) bytes[i] = (uint8_t)(i % 251);
    uint8_t digest[32]; owned_sha256(bytes, length, digest);
    assert(!owned_win_input_prepare(&slot, &child, &security, bytes, length));
    assert(slot.input_contract_v3 && slot.input_len == length && !memcmp(digest, slot.input_sha256, 32));
    memset(bytes, 0xff, length); free(bytes);
    if (length) for (size_t i = 0; i < length; i++) assert(slot.input[i] == (uint8_t)(i % 251));
    return slot;
}
static void reset(void) {
    freed = closed = writes = cancellations = 0;
    write_error = completion_error = sync_count = completed = 0;
}
int main(void) {
    reset(); OwnedWinLease slot = prepare(33);
    sync_count = 7; owned_win_input_advance(&slot, 0);
    assert(slot.input_written == 7 && slot.input_pipe && write_address == slot.input);
    sync_count = 0; owned_win_input_advance(&slot, 0);
    assert(slot.input_written == 33 && !slot.input_pipe && !slot.input && freed == 1 && closed == 2);

    reset(); slot = prepare(40000); write_error = ERROR_IO_PENDING;
    owned_win_input_advance(&slot, 0);
    assert(slot.input_pending && write_count == 16384 && slot.input_written == 0);
    completion_error = ERROR_IO_INCOMPLETE; owned_win_input_advance(&slot, 0);
    assert(slot.input_pending && writes == 1 && !freed && !closed);
    completion_error = 0; completed = 11; owned_win_input_advance(&slot, 0);
    assert(slot.input_written == 11 && write_address == slot.input + 11 && writes == 2 && slot.input_pending);
    completion_error = ERROR_IO_INCOMPLETE; owned_win_input_advance(&slot, 1);
    assert(slot.input_pending && slot.input && slot.input_pipe && !closed && !freed && cancellations == 1);
    completion_error = ERROR_OPERATION_ABORTED; owned_win_input_advance(&slot, 1);
    assert(!slot.input_pending && !slot.input && !slot.input_pipe && freed == 1 && closed == 2);
    assert(!slot.runtime_error && slot.input_written == 11 && writes == 2);

    reset(); slot = prepare(40000); write_error = ERROR_IO_PENDING;
    owned_win_input_advance(&slot, 0); completed = 9;
    owned_win_input_advance(&slot, 1);
    assert(!slot.input_pipe && slot.input_written == 9 && writes == 1 && !slot.runtime_error);

    reset(); slot = prepare(40000); write_error = ERROR_IO_PENDING;
    owned_win_input_advance(&slot, 0); completed = 16385;
    owned_win_input_advance(&slot, 0);
    assert(!slot.input_pipe && !slot.input_written && slot.runtime_error == EIO && writes == 1);

    reset(); slot = prepare(40000); write_error = ERROR_IO_PENDING;
    owned_win_input_advance(&slot, 0); completion_error = ERROR_BROKEN_PIPE;
    owned_win_input_advance(&slot, 0);
    assert(!slot.input_pipe && slot.runtime_error == EPIPE && freed == 1);

    reset(); slot = prepare(40000); write_error = ERROR_IO_PENDING;
    owned_win_input_advance(&slot, 0); completion_error = ERROR_BROKEN_PIPE;
    owned_win_input_advance(&slot, 1);
    assert(!slot.input_pipe && !slot.runtime_error && freed == 1);

    reset(); slot = prepare(0);
    assert(!slot.input_pipe && !slot.input && closed == 2 && !freed);
    owned_win_input_advance(&slot, 0); assert(!writes && !slot.runtime_error);
    puts("PASS: portable Windows stdin transport fakes: snapshot, partial writes, pending ownership, cancel races, EOF");
    return 0;
}
