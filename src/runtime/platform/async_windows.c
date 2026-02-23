/*
 * Async I/O Driver — Windows IOCP Backend
 *
 * All-IOCP (I/O Completion Port) implementation:
 *   - Network:  WSARecv/WSASend with OVERLAPPED, AcceptEx/ConnectEx
 *   - File I/O: ReadFile/WriteFile with OVERLAPPED
 *   - sendfile: TransmitFile with OVERLAPPED
 *   - Timers:   tracked deadline + GQCSE timeout parameter
 *   - flush:    no-op (all ops are submitted directly to IOCP)
 *   - poll:     GetQueuedCompletionStatusEx() batch dequeue
 *
 * IOCP is natively completion-based, so no readiness-to-completion emulation needed.
 * The iocp_op structure starts with OVERLAPPED so it can be cast directly from
 * the LPOVERLAPPED returned by GQCSE.
 */

#if defined(_WIN32)

#include "async_driver.h"

#include <winsock2.h>
#include <ws2tcpip.h>
#include <mswsock.h>
#include <windows.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ================================================================
 * Operation Types
 * ================================================================ */

#define OP_ACCEPT   1
#define OP_CONNECT  2
#define OP_RECV     3
#define OP_SEND     4
#define OP_SENDFILE 5
#define OP_READ     6
#define OP_WRITE    7
#define OP_OPEN     8
#define OP_CLOSE    9
#define OP_FSYNC    10
#define OP_TIMEOUT  11

/* ================================================================
 * Per-Operation Structure
 * ================================================================ */

typedef struct iocp_op {
    OVERLAPPED  overlapped;     /* must be first for CONTAINING_RECORD */
    int64_t     op_id;
    int         op_type;
    WSABUF      wsa_buf;
    char*       buf;
    int64_t     buf_len;
    SOCKET      accept_sock;    /* for AcceptEx: the new client socket */
    char        accept_buf[128];/* AcceptEx address buffer */
    SOCKET      fd;             /* the primary socket or INVALID_SOCKET */
    HANDLE      file_handle;    /* for file ops: the file HANDLE */
    int64_t     offset;         /* file offset for read/write */
    int64_t     sock_fd;        /* for sendfile: target socket */
    int64_t     file_fd;        /* for sendfile: source file handle */
    int64_t     sendfile_len;   /* for sendfile: byte count */
    char*       path;           /* for open: owned copy */
    int64_t     open_flags;     /* for open */
    int64_t     open_mode;      /* for open */
    const char* addr;           /* for connect: owned copy */
    int64_t     port;           /* for connect */
    int64_t     timeout_ms;     /* for timeout */
    int         completed;      /* 1 if synchronously completed */
    int64_t     result;         /* completion result */
} iocp_op;

/* ================================================================
 * Driver Structure
 * ================================================================ */

typedef struct {
    spl_driver          base;
    HANDLE              iocp;

    /* open-addressing hash table of iocp_op pointers */
    iocp_op**           ops;
    int64_t             ops_cap;
    int64_t             ops_count;

    /* Function pointers loaded via WSAIoctl */
    LPFN_ACCEPTEX       lpfnAcceptEx;
    LPFN_CONNECTEX      lpfnConnectEx;

    /* Pending timer ops: linear scan (timers are rare) */
    iocp_op**           timers;
    int64_t             timer_count;
    int64_t             timer_cap;
} iocp_driver;

/* ================================================================
 * Hash Table Helpers (keyed by op_id, values are heap iocp_op*)
 * ================================================================ */

static int64_t hash_slot(int64_t op_id, int64_t cap) {
    return (uint64_t)op_id % (uint64_t)cap;
}

static iocp_op* find_op(iocp_driver* id, int64_t op_id) {
    int64_t idx = hash_slot(op_id, id->ops_cap);
    for (int64_t i = 0; i < id->ops_cap; i++) {
        int64_t slot = (idx + i) % id->ops_cap;
        if (id->ops[slot] && id->ops[slot]->op_id == op_id)
            return id->ops[slot];
        if (!id->ops[slot])
            return NULL;
    }
    return NULL;
}

static int insert_op_table(iocp_driver* id, iocp_op* op) {
    if (id->ops_count * 2 >= id->ops_cap) {
        int64_t new_cap = id->ops_cap * 2;
        iocp_op** new_ops = (iocp_op**)calloc((size_t)new_cap, sizeof(iocp_op*));
        if (!new_ops) return -1;
        for (int64_t i = 0; i < id->ops_cap; i++) {
            if (id->ops[i]) {
                int64_t s = hash_slot(id->ops[i]->op_id, new_cap);
                while (new_ops[s])
                    s = (s + 1) % new_cap;
                new_ops[s] = id->ops[i];
            }
        }
        free(id->ops);
        id->ops = new_ops;
        id->ops_cap = new_cap;
    }
    int64_t idx = hash_slot(op->op_id, id->ops_cap);
    while (id->ops[idx])
        idx = (idx + 1) % id->ops_cap;
    id->ops[idx] = op;
    id->ops_count++;
    return 0;
}

static void remove_op_table(iocp_driver* id, int64_t op_id) {
    int64_t idx = hash_slot(op_id, id->ops_cap);
    for (int64_t i = 0; i < id->ops_cap; i++) {
        int64_t slot = (idx + i) % id->ops_cap;
        if (id->ops[slot] && id->ops[slot]->op_id == op_id) {
            id->ops[slot] = NULL;
            id->ops_count--;
            /* rehash cluster */
            int64_t next = (slot + 1) % id->ops_cap;
            while (id->ops[next]) {
                iocp_op* tmp = id->ops[next];
                id->ops[next] = NULL;
                id->ops_count--;
                insert_op_table(id, tmp);
                next = (next + 1) % id->ops_cap;
            }
            return;
        }
        if (!id->ops[slot]) return;
    }
}

/* ================================================================
 * Helpers
 * ================================================================ */

static int64_t next_id(iocp_driver* id) {
    return ++id->base.next_op_id;
}

static iocp_op* alloc_op(iocp_driver* id, int op_type) {
    iocp_op* op = (iocp_op*)calloc(1, sizeof(iocp_op));
    if (!op) return NULL;
    op->op_id = next_id(id);
    op->op_type = op_type;
    op->fd = INVALID_SOCKET;
    op->file_handle = INVALID_HANDLE_VALUE;
    op->accept_sock = INVALID_SOCKET;
    if (insert_op_table(id, op) != 0) { free(op); return NULL; }
    return op;
}

static void free_op(iocp_op* op) {
    if (!op) return;
    if (op->buf) free(op->buf);
    if (op->path) free(op->path);
    if (op->addr) free((void*)op->addr);
    free(op);
}

static void load_extension_functions(iocp_driver* id) {
    SOCKET s = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (s == INVALID_SOCKET) return;

    DWORD bytes = 0;
    GUID acceptex_guid = WSAID_ACCEPTEX;
    WSAIoctl(s, SIO_GET_EXTENSION_FUNCTION_POINTER,
             &acceptex_guid, sizeof(acceptex_guid),
             &id->lpfnAcceptEx, sizeof(id->lpfnAcceptEx),
             &bytes, NULL, NULL);

    GUID connectex_guid = WSAID_CONNECTEX;
    WSAIoctl(s, SIO_GET_EXTENSION_FUNCTION_POINTER,
             &connectex_guid, sizeof(connectex_guid),
             &id->lpfnConnectEx, sizeof(id->lpfnConnectEx),
             &bytes, NULL, NULL);

    closesocket(s);
}

/* Associate a socket with the IOCP */
static int associate_socket(iocp_driver* id, SOCKET s) {
    HANDLE h = CreateIoCompletionPort((HANDLE)s, id->iocp, 0, 0);
    return (h != NULL) ? 0 : -1;
}

/* Associate a file HANDLE with the IOCP */
static int associate_handle(iocp_driver* id, HANDLE h) {
    HANDLE r = CreateIoCompletionPort(h, id->iocp, 0, 0);
    return (r != NULL) ? 0 : -1;
}

/* ================================================================
 * VTable Implementations — Destroy
 * ================================================================ */

static void iocp_destroy(spl_driver* d) {
    iocp_driver* id = (iocp_driver*)d;

    /* free all pending ops */
    for (int64_t i = 0; i < id->ops_cap; i++) {
        if (id->ops[i]) {
            if (id->ops[i]->accept_sock != INVALID_SOCKET)
                closesocket(id->ops[i]->accept_sock);
            free_op(id->ops[i]);
        }
    }
    free(id->ops);

    /* free timers */
    for (int64_t i = 0; i < id->timer_count; i++) {
        if (id->timers[i]) free_op(id->timers[i]);
    }
    free(id->timers);

    if (id->iocp) CloseHandle(id->iocp);
    free(id);
}

/* ================================================================
 * VTable Implementations — Submit
 * ================================================================ */

static int64_t iocp_submit_accept(spl_driver* d, int64_t listen_fd) {
    iocp_driver* id = (iocp_driver*)d;
    if (!id->lpfnAcceptEx) return -ENOTSUP;

    iocp_op* op = alloc_op(id, OP_ACCEPT);
    if (!op) return -ENOMEM;
    op->fd = (SOCKET)listen_fd;

    /* Create accept socket */
    op->accept_sock = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (op->accept_sock == INVALID_SOCKET) {
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -EMFILE;
    }

    DWORD bytes = 0;
    BOOL ok = id->lpfnAcceptEx(
        op->fd, op->accept_sock,
        op->accept_buf, 0,
        sizeof(struct sockaddr_in) + 16,
        sizeof(struct sockaddr_in) + 16,
        &bytes, &op->overlapped);

    if (!ok && WSAGetLastError() != ERROR_IO_PENDING) {
        int err = WSAGetLastError();
        closesocket(op->accept_sock);
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -err;
    }

    return op->op_id;
}

static int64_t iocp_submit_connect(spl_driver* d, int64_t fd,
                                    const char* addr, int64_t port) {
    iocp_driver* id = (iocp_driver*)d;
    if (!id->lpfnConnectEx) return -ENOTSUP;

    iocp_op* op = alloc_op(id, OP_CONNECT);
    if (!op) return -ENOMEM;
    op->fd = (SOCKET)fd;
    op->addr = _strdup(addr);
    op->port = port;

    /* ConnectEx requires the socket to be bound first */
    struct sockaddr_in bind_addr;
    memset(&bind_addr, 0, sizeof(bind_addr));
    bind_addr.sin_family = AF_INET;
    bind_addr.sin_addr.s_addr = INADDR_ANY;
    bind_addr.sin_port = 0;
    bind(op->fd, (struct sockaddr*)&bind_addr, sizeof(bind_addr));

    /* Associate socket with IOCP */
    associate_socket(id, op->fd);

    struct sockaddr_in sa;
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_port = htons((u_short)port);
    inet_pton(AF_INET, addr, &sa.sin_addr);

    DWORD bytes = 0;
    BOOL ok = id->lpfnConnectEx(
        op->fd, (struct sockaddr*)&sa, sizeof(sa),
        NULL, 0, &bytes, &op->overlapped);

    if (!ok && WSAGetLastError() != ERROR_IO_PENDING) {
        int err = WSAGetLastError();
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -err;
    }

    return op->op_id;
}

static int64_t iocp_submit_recv(spl_driver* d, int64_t fd, int64_t buf_size) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_RECV);
    if (!op) return -ENOMEM;
    op->fd = (SOCKET)fd;
    op->buf = (char*)malloc((size_t)buf_size);
    if (!op->buf) {
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -ENOMEM;
    }
    op->buf_len = buf_size;
    op->wsa_buf.buf = op->buf;
    op->wsa_buf.len = (ULONG)buf_size;

    associate_socket(id, op->fd);

    DWORD flags = 0;
    int rc = WSARecv(op->fd, &op->wsa_buf, 1, NULL, &flags,
                     &op->overlapped, NULL);

    if (rc == SOCKET_ERROR && WSAGetLastError() != WSA_IO_PENDING) {
        int err = WSAGetLastError();
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -err;
    }

    return op->op_id;
}

static int64_t iocp_submit_send(spl_driver* d, int64_t fd,
                                 const char* data, int64_t len) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_SEND);
    if (!op) return -ENOMEM;
    op->fd = (SOCKET)fd;
    op->buf = (char*)malloc((size_t)len);
    if (!op->buf) {
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -ENOMEM;
    }
    memcpy(op->buf, data, (size_t)len);
    op->buf_len = len;
    op->wsa_buf.buf = op->buf;
    op->wsa_buf.len = (ULONG)len;

    associate_socket(id, op->fd);

    int rc = WSASend(op->fd, &op->wsa_buf, 1, NULL, 0,
                     &op->overlapped, NULL);

    if (rc == SOCKET_ERROR && WSAGetLastError() != WSA_IO_PENDING) {
        int err = WSAGetLastError();
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -err;
    }

    return op->op_id;
}

static int64_t iocp_submit_sendfile(spl_driver* d, int64_t sock_fd,
                                     int64_t file_fd, int64_t offset,
                                     int64_t len) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_SENDFILE);
    if (!op) return -ENOMEM;
    op->fd = (SOCKET)sock_fd;
    op->file_handle = (HANDLE)(intptr_t)file_fd;
    op->offset = offset;
    op->sendfile_len = len;

    associate_socket(id, op->fd);

    /* Set file offset in OVERLAPPED */
    op->overlapped.Offset = (DWORD)(offset & 0xFFFFFFFF);
    op->overlapped.OffsetHigh = (DWORD)((offset >> 32) & 0xFFFFFFFF);

    BOOL ok = TransmitFile(
        op->fd, op->file_handle,
        (DWORD)len, 0,
        &op->overlapped, NULL, TF_USE_KERNEL_APC);

    if (!ok && WSAGetLastError() != WSA_IO_PENDING) {
        int err = WSAGetLastError();
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -err;
    }

    return op->op_id;
}

static int64_t iocp_submit_read(spl_driver* d, int64_t fd,
                                 int64_t buf_size, int64_t offset) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_READ);
    if (!op) return -ENOMEM;
    op->file_handle = (HANDLE)(intptr_t)fd;
    op->buf = (char*)malloc((size_t)buf_size);
    if (!op->buf) {
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -ENOMEM;
    }
    op->buf_len = buf_size;
    op->offset = offset;

    associate_handle(id, op->file_handle);

    op->overlapped.Offset = (DWORD)(offset & 0xFFFFFFFF);
    op->overlapped.OffsetHigh = (DWORD)((offset >> 32) & 0xFFFFFFFF);

    BOOL ok = ReadFile(op->file_handle, op->buf, (DWORD)buf_size,
                       NULL, &op->overlapped);

    if (!ok && GetLastError() != ERROR_IO_PENDING) {
        DWORD err = GetLastError();
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -(int64_t)err;
    }

    return op->op_id;
}

static int64_t iocp_submit_write(spl_driver* d, int64_t fd,
                                  const char* data, int64_t len,
                                  int64_t offset) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_WRITE);
    if (!op) return -ENOMEM;
    op->file_handle = (HANDLE)(intptr_t)fd;
    op->buf = (char*)malloc((size_t)len);
    if (!op->buf) {
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -ENOMEM;
    }
    memcpy(op->buf, data, (size_t)len);
    op->buf_len = len;
    op->offset = offset;

    associate_handle(id, op->file_handle);

    op->overlapped.Offset = (DWORD)(offset & 0xFFFFFFFF);
    op->overlapped.OffsetHigh = (DWORD)((offset >> 32) & 0xFFFFFFFF);

    BOOL ok = WriteFile(op->file_handle, op->buf, (DWORD)len,
                        NULL, &op->overlapped);

    if (!ok && GetLastError() != ERROR_IO_PENDING) {
        DWORD err = GetLastError();
        int64_t oid = op->op_id;
        remove_op_table(id, oid);
        free_op(op);
        return -(int64_t)err;
    }

    return op->op_id;
}

static int64_t iocp_submit_open(spl_driver* d, const char* path,
                                 int64_t flags, int64_t mode) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_OPEN);
    if (!op) return -ENOMEM;
    op->path = _strdup(path);
    op->open_flags = flags;
    op->open_mode = mode;

    /*
     * File open is synchronous on Windows (CreateFile doesn't use IOCP).
     * We complete it immediately and mark it as done.
     */
    DWORD access = GENERIC_READ | GENERIC_WRITE;
    DWORD share = FILE_SHARE_READ | FILE_SHARE_WRITE;
    DWORD disposition = OPEN_EXISTING;

    /* Map common POSIX-like flag combinations */
    if (flags & 0x0200) { /* O_CREAT */
        if (flags & 0x0400) /* O_EXCL */
            disposition = CREATE_NEW;
        else
            disposition = OPEN_ALWAYS;
    }
    if (flags & 0x0800) /* O_TRUNC */
        disposition = CREATE_ALWAYS;
    if ((flags & 0x03) == 0) /* O_RDONLY */
        access = GENERIC_READ;
    else if ((flags & 0x03) == 1) /* O_WRONLY */
        access = GENERIC_WRITE;

    HANDLE fh = CreateFileA(
        path, access, share, NULL, disposition,
        FILE_ATTRIBUTE_NORMAL | FILE_FLAG_OVERLAPPED,
        NULL);

    if (fh == INVALID_HANDLE_VALUE) {
        op->result = -(int64_t)GetLastError();
    } else {
        op->result = (int64_t)(intptr_t)fh;
    }
    op->completed = 1;

    return op->op_id;
}

static int64_t iocp_submit_close(spl_driver* d, int64_t fd) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_CLOSE);
    if (!op) return -ENOMEM;
    op->file_handle = (HANDLE)(intptr_t)fd;

    /* Close is synchronous */
    BOOL ok = CloseHandle(op->file_handle);
    op->result = ok ? 0 : -(int64_t)GetLastError();
    op->completed = 1;

    return op->op_id;
}

static int64_t iocp_submit_fsync(spl_driver* d, int64_t fd) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_FSYNC);
    if (!op) return -ENOMEM;
    op->file_handle = (HANDLE)(intptr_t)fd;

    /* FlushFileBuffers is synchronous */
    BOOL ok = FlushFileBuffers(op->file_handle);
    op->result = ok ? 0 : -(int64_t)GetLastError();
    op->completed = 1;

    return op->op_id;
}

static int64_t iocp_submit_timeout(spl_driver* d, int64_t timeout_ms) {
    iocp_driver* id = (iocp_driver*)d;

    iocp_op* op = alloc_op(id, OP_TIMEOUT);
    if (!op) return -ENOMEM;
    op->timeout_ms = timeout_ms;

    /*
     * Track timer in a separate list. During poll, we compute the GQCSE
     * timeout as the minimum of all pending timer deadlines, and fire
     * expired timers as completions.
     */
    LARGE_INTEGER freq, now;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&now);
    /* Store absolute deadline in offset field (in QPC ticks) */
    op->offset = now.QuadPart + (timeout_ms * freq.QuadPart) / 1000;

    /* Add to timer list */
    if (id->timer_count >= id->timer_cap) {
        int64_t new_cap = id->timer_cap ? id->timer_cap * 2 : 16;
        iocp_op** new_timers = (iocp_op**)realloc(
            id->timers, sizeof(iocp_op*) * (size_t)new_cap);
        if (!new_timers) {
            int64_t oid = op->op_id;
            remove_op_table(id, oid);
            free_op(op);
            return -ENOMEM;
        }
        id->timers = new_timers;
        id->timer_cap = new_cap;
    }
    id->timers[id->timer_count++] = op;

    return op->op_id;
}

/* ================================================================
 * Flush — no-op for IOCP (ops submitted directly)
 * ================================================================ */

static int64_t iocp_flush(spl_driver* d) {
    (void)d;
    return 0;
}

/* ================================================================
 * Poll — GetQueuedCompletionStatusEx + timer check
 * ================================================================ */

static int64_t iocp_poll(spl_driver* d, spl_completion* out, int64_t max,
                          int64_t timeout_ms) {
    iocp_driver* id = (iocp_driver*)d;
    int64_t count = 0;

    /* 1. Drain synchronously completed ops (open, close, fsync) */
    for (int64_t i = 0; i < id->ops_cap && count < max; i++) {
        if (id->ops[i] && id->ops[i]->completed) {
            out[count++] = (spl_completion){
                .id = id->ops[i]->op_id,
                .result = id->ops[i]->result,
                .flags = 0
            };
            int64_t oid = id->ops[i]->op_id;
            iocp_op* to_free = id->ops[i];
            remove_op_table(id, oid);
            free_op(to_free);
        }
    }

    /* 2. Check expired timers */
    LARGE_INTEGER freq, now;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&now);
    int64_t min_timer_wait_ms = -1;

    for (int64_t i = 0; i < id->timer_count && count < max; ) {
        iocp_op* t = id->timers[i];
        if (now.QuadPart >= t->offset) {
            /* Timer expired */
            out[count++] = (spl_completion){
                .id = t->op_id, .result = 0, .flags = 0
            };
            int64_t oid = t->op_id;
            remove_op_table(id, oid);
            free_op(t);
            /* swap-remove from timer array */
            id->timers[i] = id->timers[--id->timer_count];
        } else {
            /* Compute remaining wait */
            int64_t remaining_ticks = t->offset - now.QuadPart;
            int64_t remaining_ms = (remaining_ticks * 1000) / freq.QuadPart;
            if (remaining_ms < 0) remaining_ms = 0;
            if (min_timer_wait_ms < 0 || remaining_ms < min_timer_wait_ms)
                min_timer_wait_ms = remaining_ms;
            i++;
        }
    }

    if (count >= max) return count;

    /* 3. Compute effective GQCSE timeout */
    DWORD gqcse_timeout;
    if (timeout_ms == 0) {
        gqcse_timeout = 0;
    } else if (timeout_ms < 0) {
        /* Block forever, but respect timer deadlines */
        if (min_timer_wait_ms >= 0)
            gqcse_timeout = (DWORD)min_timer_wait_ms;
        else
            gqcse_timeout = INFINITE;
    } else {
        gqcse_timeout = (DWORD)timeout_ms;
        if (min_timer_wait_ms >= 0 && min_timer_wait_ms < timeout_ms)
            gqcse_timeout = (DWORD)min_timer_wait_ms;
    }

    /* If we already have completions and non-blocking requested, return */
    if (count > 0 && timeout_ms == 0) return count;

    /* 4. Batch dequeue from IOCP */
    ULONG iocp_max = (ULONG)(max - count);
    if (iocp_max == 0) return count;

    OVERLAPPED_ENTRY* entries = (OVERLAPPED_ENTRY*)malloc(
        sizeof(OVERLAPPED_ENTRY) * iocp_max);
    if (!entries) return count;

    ULONG removed = 0;
    BOOL ok = GetQueuedCompletionStatusEx(
        id->iocp, entries, iocp_max, &removed,
        gqcse_timeout, FALSE);

    if (ok && removed > 0) {
        for (ULONG i = 0; i < removed && count < max; i++) {
            OVERLAPPED* ovl = entries[i].lpOverlapped;
            if (!ovl) continue;

            /* Recover iocp_op from OVERLAPPED (it's the first member) */
            iocp_op* op = (iocp_op*)ovl;
            DWORD transferred = entries[i].dwNumberOfBytesTransferred;

            int64_t result;
            if (ovl->Internal == 0) {
                /* Success */
                switch (op->op_type) {
                case OP_ACCEPT:
                    /* Update the accept socket's context */
                    setsockopt(op->accept_sock, SOL_SOCKET,
                               SO_UPDATE_ACCEPT_CONTEXT,
                               (char*)&op->fd, sizeof(op->fd));
                    result = (int64_t)op->accept_sock;
                    op->accept_sock = INVALID_SOCKET; /* prevent double-close */
                    break;
                case OP_CONNECT:
                    setsockopt(op->fd, SOL_SOCKET,
                               SO_UPDATE_CONNECT_CONTEXT, NULL, 0);
                    result = 0;
                    break;
                default:
                    result = (int64_t)transferred;
                    break;
                }
            } else {
                /* Error: NTSTATUS in Internal, map to negative */
                result = -(int64_t)ovl->Internal;
            }

            out[count++] = (spl_completion){
                .id = op->op_id, .result = result, .flags = 0
            };
            int64_t oid = op->op_id;
            remove_op_table(id, oid);
            free_op(op);
        }
    }

    free(entries);

    /* 5. Re-check timers after GQCSE wait */
    if (min_timer_wait_ms >= 0 && count < max) {
        QueryPerformanceCounter(&now);
        for (int64_t i = 0; i < id->timer_count && count < max; ) {
            iocp_op* t = id->timers[i];
            if (now.QuadPart >= t->offset) {
                out[count++] = (spl_completion){
                    .id = t->op_id, .result = 0, .flags = 0
                };
                int64_t oid = t->op_id;
                remove_op_table(id, oid);
                free_op(t);
                id->timers[i] = id->timers[--id->timer_count];
            } else {
                i++;
            }
        }
    }

    return count;
}

/* ================================================================
 * Cancel
 * ================================================================ */

static bool iocp_cancel(spl_driver* d, int64_t op_id) {
    iocp_driver* id = (iocp_driver*)d;
    iocp_op* op = find_op(id, op_id);
    if (!op) return false;

    /* Check timers first */
    for (int64_t i = 0; i < id->timer_count; i++) {
        if (id->timers[i] && id->timers[i]->op_id == op_id) {
            remove_op_table(id, op_id);
            free_op(id->timers[i]);
            id->timers[i] = id->timers[--id->timer_count];
            return true;
        }
    }

    /* Cancel I/O on the handle */
    if (op->op_type == OP_RECV || op->op_type == OP_SEND ||
        op->op_type == OP_ACCEPT || op->op_type == OP_CONNECT ||
        op->op_type == OP_SENDFILE) {
        CancelIoEx((HANDLE)op->fd, &op->overlapped);
    } else if (op->op_type == OP_READ || op->op_type == OP_WRITE) {
        CancelIoEx(op->file_handle, &op->overlapped);
    }

    /* Note: the cancelled completion will arrive via GQCSE with an error status.
     * We leave the op in the table to be cleaned up when the cancellation
     * completion arrives in poll(). */
    return true;
}

/* ================================================================
 * Query
 * ================================================================ */

static const char* iocp_backend_name(spl_driver* d) {
    (void)d;
    return "iocp";
}

static spl_backend_type iocp_backend_type_fn(spl_driver* d) {
    (void)d;
    return SPL_BACKEND_IOCP;
}

static bool iocp_supports_sendfile(spl_driver* d) {
    (void)d;
    return true;  /* TransmitFile */
}

static bool iocp_supports_zero_copy(spl_driver* d) {
    (void)d;
    return true;  /* TransmitFile is zero-copy via kernel APC */
}

/* ================================================================
 * VTable
 * ================================================================ */

static const spl_driver_vtable iocp_vtable = {
    .destroy           = iocp_destroy,
    .submit_accept     = iocp_submit_accept,
    .submit_connect    = iocp_submit_connect,
    .submit_recv       = iocp_submit_recv,
    .submit_send       = iocp_submit_send,
    .submit_sendfile   = iocp_submit_sendfile,
    .submit_read       = iocp_submit_read,
    .submit_write      = iocp_submit_write,
    .submit_open       = iocp_submit_open,
    .submit_close      = iocp_submit_close,
    .submit_fsync      = iocp_submit_fsync,
    .submit_timeout    = iocp_submit_timeout,
    .flush             = iocp_flush,
    .poll              = iocp_poll,
    .cancel            = iocp_cancel,
    .backend_name      = iocp_backend_name,
    .backend_type_fn   = iocp_backend_type_fn,
    .supports_sendfile = iocp_supports_sendfile,
    .supports_zero_copy = iocp_supports_zero_copy,
};

/* ================================================================
 * Constructor
 * ================================================================ */

spl_driver* spl_driver_create_iocp(int64_t queue_depth) {
    if (queue_depth <= 0) queue_depth = 256;

    /* Ensure Winsock is initialized */
    WSADATA wsa;
    if (WSAStartup(MAKEWORD(2, 2), &wsa) != 0)
        return NULL;

    HANDLE iocp = CreateIoCompletionPort(
        INVALID_HANDLE_VALUE, NULL, 0, 0);
    if (!iocp) return NULL;

    iocp_driver* id = (iocp_driver*)calloc(1, sizeof(iocp_driver));
    if (!id) { CloseHandle(iocp); return NULL; }

    id->base.vtable = &iocp_vtable;
    id->base.next_op_id = 0;
    id->iocp = iocp;

    /* hash table */
    id->ops_cap = queue_depth * 2;
    id->ops = (iocp_op**)calloc((size_t)id->ops_cap, sizeof(iocp_op*));
    if (!id->ops) { CloseHandle(iocp); free(id); return NULL; }
    id->ops_count = 0;

    /* timer list */
    id->timer_cap = 16;
    id->timers = (iocp_op**)calloc((size_t)id->timer_cap, sizeof(iocp_op*));
    if (!id->timers) {
        free(id->ops); CloseHandle(iocp); free(id);
        return NULL;
    }
    id->timer_count = 0;

    /* Load AcceptEx and ConnectEx */
    load_extension_functions(id);

    return (spl_driver*)id;
}

#endif /* defined(_WIN32) */
