/* Private Windows immutable stdin transport. The including owner provides
 * OwnedWinLease, the registry lock, SHA-256 and allocation/Win32 helpers. */
static void owned_win_input_close(OwnedWinLease* slot) {
    /* CancelIoEx does not complete I/O. Never close/free an in-flight write. */
    if (slot->input_pending) return;
    owned_win_close(&slot->input_pipe);
    owned_win_close(&slot->input_io.hEvent);
    RT_OWNED_HOST_FREE(slot->input); slot->input = NULL;
}

static void owned_win_input_advance(OwnedWinLease* slot, int stop) {
    if (!slot->input_pipe) return;
    if (stop) slot->input_stopping = 1;
    if (slot->input_pending) {
        if (slot->input_stopping) (void)CancelIoEx(slot->input_pipe, &slot->input_io);
        DWORD written = 0;
        if (!GetOverlappedResult(slot->input_pipe, &slot->input_io, &written, FALSE)) {
            DWORD error = GetLastError();
            if (error == ERROR_IO_INCOMPLETE) return;
            slot->input_pending = 0;
            if (!(slot->input_stopping && (error == ERROR_OPERATION_ABORTED ||
                error == ERROR_BROKEN_PIPE || error == ERROR_NO_DATA)))
                owned_win_lease_error(slot, error == ERROR_BROKEN_PIPE || error == ERROR_NO_DATA ? EPIPE : EIO);
            owned_win_input_close(slot); return;
        }
        slot->input_pending = 0;
        if (!written || written > slot->input_requested) {
            owned_win_lease_error(slot, EIO); owned_win_input_close(slot); return;
        }
        slot->input_written += written;
    }
    if (slot->input_stopping || slot->input_written == slot->input_len) {
        owned_win_input_close(slot); return;
    }
    /* One bounded write per poll. Even a child that never reads cannot block
     * this registry lock. The stable slot owns OVERLAPPED and copied bytes. */
    DWORD count = (DWORD)(slot->input_len - slot->input_written);
    if (count > 16384) count = 16384;
    HANDLE event = slot->input_io.hEvent;
    memset(&slot->input_io, 0, sizeof(slot->input_io)); slot->input_io.hEvent = event;
    ResetEvent(event);
    DWORD written = 0; slot->input_requested = count;
    if (WriteFile(slot->input_pipe, slot->input + slot->input_written, count, &written, &slot->input_io)) {
        if (!written || written > count) owned_win_lease_error(slot, EIO);
        else slot->input_written += written;
        if (!written || written > count || slot->input_written == slot->input_len)
            owned_win_input_close(slot);
    } else {
        DWORD error = GetLastError();
        if (error == ERROR_IO_PENDING) slot->input_pending = 1;
        else {
            owned_win_lease_error(slot, error == ERROR_BROKEN_PIPE || error == ERROR_NO_DATA ? EPIPE : EIO);
            owned_win_input_close(slot);
        }
    }
}

static int owned_win_input_prepare(OwnedWinLease* slot, HANDLE* child_input,
                                    SECURITY_ATTRIBUTES* security,
                                    const uint8_t* input, uint64_t input_len) {
    if (input_len) {
        slot->input = (uint8_t*)RT_OWNED_HOST_MALLOC((size_t)input_len);
        if (!slot->input) return ENOMEM;
        memcpy(slot->input, input, (size_t)input_len);
    }
    slot->input_contract_v3 = 1; slot->input_len = input_len;
    owned_sha256(slot->input, (size_t)input_len, slot->input_sha256);
    /* Use independent entropy: the child can query its pipe name, but must
     * never learn the private process lease capability from it. */
    RtOwnedProcessTokenV2 nonce;
    if (!owned_win_random_token(&nonce)) return EIO;
    WCHAR name[128];
    swprintf(name, sizeof(name) / sizeof(name[0]), L"\\\\.\\pipe\\simple-owned-input-%016llx%016llx",
        (unsigned long long)nonce.high, (unsigned long long)nonce.low);
    slot->input_pipe = CreateNamedPipeW(name,
        PIPE_ACCESS_OUTBOUND | FILE_FLAG_OVERLAPPED | FILE_FLAG_FIRST_PIPE_INSTANCE,
        PIPE_TYPE_BYTE | PIPE_READMODE_BYTE | PIPE_WAIT | PIPE_REJECT_REMOTE_CLIENTS,
        1, 16384, 16384, 0, NULL);
    if (slot->input_pipe == INVALID_HANDLE_VALUE) { slot->input_pipe = NULL; return EIO; }
    slot->input_io.hEvent = CreateEventW(NULL, TRUE, FALSE, NULL);
    if (!slot->input_io.hEvent) return EIO;
    *child_input = CreateFileW(name, GENERIC_READ, 0, security, OPEN_EXISTING, 0, NULL);
    if (*child_input == INVALID_HANDLE_VALUE) return EIO;
    /* Successful CreateFileW established the connection; keep that private
     * read handle open through admission. No redundant ConnectNamedPipe is
     * issued, so admission can never leave a pending connect OVERLAPPED. */
    if (!input_len) owned_win_input_close(slot);
    return 0;
}
