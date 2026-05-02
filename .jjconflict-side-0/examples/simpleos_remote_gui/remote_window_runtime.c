#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);

#ifndef APP_TITLE
#define APP_TITLE "SimpleOS App"
#endif

#ifndef APP_ID
#define APP_ID "/sys/apps/app"
#endif

#ifndef APP_CONTENT
#define APP_CONTENT "Filesystem-backed user process"
#endif

#ifndef APP_WIDTH
#define APP_WIDTH 420
#endif

#ifndef APP_HEIGHT
#define APP_HEIGHT 240
#endif

#ifndef APP_POS_X
#define APP_POS_X 96
#endif

#ifndef APP_POS_Y
#define APP_POS_Y 96
#endif

#ifndef APP_MARKER
#define APP_MARKER ""
#endif

#ifndef APP_PRE_WINDOW_HOOK
#define APP_PRE_WINDOW_HOOK() 0
#endif

#ifndef APP_RUNTIME_CONTENT
#define APP_RUNTIME_CONTENT(argc, argv) APP_CONTENT
#endif

#define SYS_IPC_SEND 20
#define SYS_IPC_RECV 21
#define SYS_IPC_CREATE_PORT 22
#define SYS_IPC_CONNECT 23

#define COMP_CREATE_WINDOW 1
#define COMP_DESTROY_WINDOW 2
#define COMP_UPDATE_TREE 3
#define COMP_CLOSE_REQUEST 12

static size_t _strlen_local(const char *s) {
    size_t n = 0;
    while (s[n] != '\0') n++;
    return n;
}

static void _push_u32(uint8_t *buf, size_t *offset, uint32_t value) {
    buf[(*offset)++] = (uint8_t)(value & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 8) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 16) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 24) & 0xFFu);
}

static void _push_i32(uint8_t *buf, size_t *offset, int32_t value) {
    _push_u32(buf, offset, (uint32_t)value);
}

static void _push_u64(uint8_t *buf, size_t *offset, uint64_t value) {
    buf[(*offset)++] = (uint8_t)(value & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 8) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 16) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 24) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 32) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 40) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 48) & 0xFFu);
    buf[(*offset)++] = (uint8_t)((value >> 56) & 0xFFu);
}

static uint32_t _read_u32(const uint8_t *ptr) {
    return ((uint32_t)ptr[0]) |
           ((uint32_t)ptr[1] << 8) |
           ((uint32_t)ptr[2] << 16) |
           ((uint32_t)ptr[3] << 24);
}

static uint64_t _read_u64(const uint8_t *ptr) {
    return ((uint64_t)ptr[0]) |
           ((uint64_t)ptr[1] << 8) |
           ((uint64_t)ptr[2] << 16) |
           ((uint64_t)ptr[3] << 24) |
           ((uint64_t)ptr[4] << 32) |
           ((uint64_t)ptr[5] << 40) |
           ((uint64_t)ptr[6] << 48) |
           ((uint64_t)ptr[7] << 56);
}

static int _ipc_send(uint64_t dst_port, uint64_t src_port, const uint8_t *data, uint64_t len) {
    return (int)simpleos_syscall(SYS_IPC_SEND, (int64_t)dst_port, (int64_t)src_port,
                                 (int64_t)(uintptr_t)data, (int64_t)len, 0);
}

static int _ipc_recv_payload(uint64_t app_port, int blocking, uint8_t *out, size_t out_cap) {
    int64_t msg_raw = simpleos_syscall(
        SYS_IPC_RECV,
        (int64_t)app_port,
        blocking ? (int64_t)0xFFFFFFFFu : 0,
        blocking ? 0 : 1,
        0,
        0
    );
    if (msg_raw <= 0) {
        return -1;
    }

    const uint8_t *msg = (const uint8_t *)(uintptr_t)msg_raw;
    uint32_t payload_len = _read_u32(msg + 24);
    const uint8_t *payload = msg + 32;
    if ((size_t)payload_len > out_cap) {
        payload_len = (uint32_t)out_cap;
    }
    for (uint32_t i = 0; i < payload_len; i++) {
        out[i] = payload[i];
    }
    return (int)payload_len;
}

static uint64_t _connect_compositor(uint64_t *app_port_out) {
    static const char kPortName[] = "compositor";
    int64_t app_port = simpleos_syscall(SYS_IPC_CREATE_PORT, 0, 0, 0, 0, 0);
    if (app_port <= 0) {
        return 0;
    }
    int64_t compositor_port = simpleos_syscall(
        SYS_IPC_CONNECT,
        (int64_t)(uintptr_t)kPortName,
        (int64_t)(_strlen_local(kPortName)),
        0, 0, 0
    );
    if (compositor_port <= 0) {
        return 0;
    }
    *app_port_out = (uint64_t)app_port;
    return (uint64_t)compositor_port;
}

static uint64_t _create_window(uint64_t compositor_port, uint64_t app_port) {
    uint8_t msg[1024];
    size_t off = 0;
    const size_t title_len = _strlen_local(APP_TITLE);
    const size_t app_id_len = _strlen_local(APP_ID);

    _push_u32(msg, &off, COMP_CREATE_WINDOW);
    _push_u32(msg, &off, (uint32_t)title_len);
    for (size_t i = 0; i < title_len; i++) {
        msg[off++] = (uint8_t)APP_TITLE[i];
    }
    _push_i32(msg, &off, APP_POS_X);
    _push_i32(msg, &off, APP_POS_Y);
    _push_i32(msg, &off, APP_WIDTH);
    _push_i32(msg, &off, APP_HEIGHT);
    _push_u64(msg, &off, (uint64_t)getpid());
    _push_u32(msg, &off, (uint32_t)app_id_len);
    for (size_t i = 0; i < app_id_len; i++) {
        msg[off++] = (uint8_t)APP_ID[i];
    }

    if (_ipc_send(compositor_port, app_port, msg, (uint64_t)off) < 0) {
        return 0;
    }

    uint8_t reply[64];
    int reply_len = _ipc_recv_payload(app_port, 1, reply, sizeof(reply));
    if (reply_len < 12) {
        return 0;
    }
    if ((int32_t)_read_u32(reply) != 0) {
        return 0;
    }
    return _read_u64(reply + 4);
}

static void _update_content(uint64_t compositor_port, uint64_t app_port, uint64_t window_id,
                            const char *content) {
    uint8_t msg[2048];
    size_t off = 0;
    size_t content_len = _strlen_local(content);
    const size_t content_cap = sizeof(msg) - 16;
    if (content_len > content_cap) {
        content_len = content_cap;
    }

    _push_u32(msg, &off, COMP_UPDATE_TREE);
    _push_u64(msg, &off, window_id);
    _push_u32(msg, &off, (uint32_t)content_len);
    for (size_t i = 0; i < content_len; i++) {
        msg[off++] = (uint8_t)content[i];
    }

    if (_ipc_send(compositor_port, app_port, msg, (uint64_t)off) >= 0) {
        uint8_t reply[32];
        (void)_ipc_recv_payload(app_port, 1, reply, sizeof(reply));
    }
}

static void _destroy_window(uint64_t compositor_port, uint64_t app_port, uint64_t window_id) {
    uint8_t msg[16];
    size_t off = 0;
    _push_u32(msg, &off, COMP_DESTROY_WINDOW);
    _push_u64(msg, &off, window_id);
    if (_ipc_send(compositor_port, app_port, msg, (uint64_t)off) >= 0) {
        uint8_t reply[32];
        (void)_ipc_recv_payload(app_port, 1, reply, sizeof(reply));
    }
}

static int _wait_for_close(uint64_t app_port, uint64_t window_id) {
    uint8_t msg[64];
    for (;;) {
        int len = _ipc_recv_payload(app_port, 1, msg, sizeof(msg));
        if (len < 12) {
            continue;
        }
        uint32_t method = _read_u32(msg);
        uint64_t target_wid = _read_u64(msg + 4);
        if (target_wid != window_id) {
            continue;
        }
        if (method == COMP_CLOSE_REQUEST) {
            return 0;
        }
    }
}

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;

    static volatile const char *marker = APP_MARKER;
    if (marker[0] == '\xff') {
        return 99;
    }
    {
        int pre_status = APP_PRE_WINDOW_HOOK();
        if (pre_status != 0) {
            return pre_status;
        }
    }

    const char *content = APP_RUNTIME_CONTENT(argc, argv);
    if (content == (const char *)0) {
        content = APP_CONTENT;
    }

    uint64_t app_port = 0;
    uint64_t compositor_port = _connect_compositor(&app_port);
    if (compositor_port == 0 || app_port == 0) {
        return 2;
    }

    uint64_t window_id = _create_window(compositor_port, app_port);
    if (window_id == 0) {
        return 3;
    }

    _update_content(compositor_port, app_port, window_id, content);
    _wait_for_close(app_port, window_id);
    _destroy_window(compositor_port, app_port, window_id);
    return 0;
}
