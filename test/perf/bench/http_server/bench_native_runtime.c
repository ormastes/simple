#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/epoll.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <stdint.h>
#include <errno.h>

/* === Tagged RuntimeValue ABI ===
 * 64-bit: [payload 61 bits][tag 3 bits]
 * TAG_INT=0, TAG_HEAP=1, TAG_FLOAT=2, TAG_SPECIAL=3
 * Integers:   (value << 3) | 0
 * Heap ptrs:  (aligned_ptr) | 1
 */
typedef uint64_t RtVal;
#define TAG_INT   0
#define TAG_HEAP  1
#define MAKE_INT(v)  ((uint64_t)((int64_t)(v) << 3) | TAG_INT)
#define MAKE_HEAP(p) ((uint64_t)(p) | TAG_HEAP)
#define GET_INT(v)   ((int64_t)(v) >> 3)
#define GET_HEAP(v)  ((void*)((v) & ~(uint64_t)7))

/* HeapHeader: 8 bytes */
typedef struct __attribute__((packed)) {
    uint8_t  object_type;  /* 0x02=Array */
    uint8_t  gc_flags;     /* bit 3=BYTE_PACKED, bit 4=U64_PACKED */
    uint16_t reserved;
    uint32_t size;
} HeapHeader;

/* RuntimeArray: HeapHeader + len + cap + data* */
typedef struct {
    HeapHeader header;
    uint64_t len;
    uint64_t capacity;
    RtVal*   data;
} RuntimeArray;

#define HEAP_ARRAY     0x02
#define GC_BYTE_PACKED 0x08
#define GC_U64_PACKED  0x10

static RuntimeArray* make_array(uint64_t cap, int is_byte) {
    RuntimeArray* a = (RuntimeArray*)calloc(1, sizeof(RuntimeArray));
    a->header.object_type = HEAP_ARRAY;
    a->header.gc_flags = is_byte ? GC_BYTE_PACKED : 0;
    a->header.size = sizeof(RuntimeArray);
    a->len = 0;
    a->capacity = cap > 0 ? cap : 16;
    a->data = (RtVal*)calloc(a->capacity, sizeof(RtVal));
    return a;
}

static RtVal array_to_val(RuntimeArray* a) {
    return MAKE_HEAP(a);
}

/* === Alloc === */
void* rt_alloc(int64_t size) { return calloc(1, size > 0 ? size : 8); }

/* === Strings — codegen passes (ptr, len) === */
const char* rt_string_new(const char* s, int64_t len) {
    if (!s || len <= 0) return strdup("");
    char* r = malloc(len + 1);
    memcpy(r, s, len);
    r[len] = 0;
    return r;
}
const char* rt_string_data(const char* s) { return s ? s : ""; }
int64_t rt_string_len(const char* s) { return s ? (int64_t)strlen(s) : 0; }
int64_t rt_string_eq(const char* a, const char* b) {
    if (!a || !b) return a == b;
    return strcmp(a, b) == 0;
}

/* === Print === */
void rt_print_str(const char* s) { if (s) fputs(s, stdout); }
void rt_println_str(const char* s) { if (s) puts(s); else puts(""); }
void rt_print_value(int64_t v) { printf("%ld", v); }
void rt_println_value(int64_t v) { printf("%ld\n", v); }
void rt_eprint_str(const char* s) { if (s) fputs(s, stderr); }
void rt_eprintln_str(const char* s) { if (s) fprintf(stderr, "%s\n", s); else fprintf(stderr, "\n"); }
void rt_eprint_value(int64_t v) { fprintf(stderr, "%ld", v); }
void rt_eprintln_value(int64_t v) { fprintf(stderr, "%ld\n", v); }

/* === Arrays (RuntimeValue-compatible) === */
RtVal rt_array_new(void) {
    return array_to_val(make_array(16, 0));
}

RtVal rt_byte_array_new(uint64_t cap) {
    return array_to_val(make_array(cap, 1));
}

int64_t rt_array_len(RtVal arr) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    return a ? (int64_t)a->len : 0;
}

RtVal rt_array_get(RtVal arr, int64_t i) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    if (!a || i < 0 || (uint64_t)i >= a->len) return MAKE_INT(0);
    return a->data[i];
}

const char* rt_array_get_text(RtVal arr, int64_t i) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    if (!a || i < 0 || (uint64_t)i >= a->len) return "";
    return (const char*)a->data[i];
}

void rt_array_push(RtVal arr, RtVal val) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    if (!a) return;
    if (a->len >= a->capacity) {
        a->capacity *= 2;
        a->data = (RtVal*)realloc(a->data, a->capacity * sizeof(RtVal));
    }
    a->data[a->len++] = val;
}

void rt_array_set_text(RtVal arr, int64_t i, const char* val) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    if (a && i >= 0 && (uint64_t)i < a->capacity)
        a->data[i] = (RtVal)(uintptr_t)val;
}

void rt_array_set_len_known_text(RtVal arr, int64_t len) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    if (a) a->len = len;
}

int64_t* rt_array_data_ptr_u8(RtVal arr) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    return a ? (int64_t*)a->data : NULL;
}
int64_t* rt_array_data_ptr_text(RtVal arr) {
    RuntimeArray* a = (RuntimeArray*)GET_HEAP(arr);
    return a ? (int64_t*)a->data : NULL;
}

/* === Comparison === */
int64_t rt_native_eq(int64_t a, int64_t b) { return a == b; }
int64_t rt_native_neq(int64_t a, int64_t b) { return a != b; }
int64_t rt_contains(const char* hay, const char* needle) {
    if (!hay || !needle) return 0;
    return strstr(hay, needle) != NULL;
}
int64_t rt_hash_text(const char* s) {
    if (!s) return 0;
    int64_t h = 5381;
    while (*s) h = h * 33 + *s++;
    return h;
}
int64_t rt_value_bool(int64_t v) { return v != 0; }

/* === Enum/Tuple stubs === */
int64_t rt_enum_new(int64_t disc, int64_t payload) {
    int64_t* p = malloc(2 * sizeof(int64_t));
    p[0] = disc; p[1] = payload;
    return (int64_t)p;
}
int64_t* rt_tuple_new(int64_t size) { return calloc(size, sizeof(int64_t)); }
void rt_tuple_set(int64_t* t, int64_t i, int64_t v) { if (t) t[i] = v; }

/* === Misc stubs === */
void rt_function_not_found(const char* name) {
    fprintf(stderr, "function not found: %s\n", name ? name : "?");
    exit(1);
}
int64_t rt_interp_call(const char* name, int64_t args) { return 0; }

/* === TCP === */
int64_t rt_io_tcp_socket_create(int64_t family) {
    return (int64_t)socket(AF_INET, SOCK_STREAM, 0);
}
int64_t rt_io_tcp_set_reuseaddr(int64_t fd, int64_t enabled) {
    int val = enabled ? 1 : 0;
    return setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &val, sizeof(val)) == 0;
}
int64_t rt_io_tcp_set_reuseport(int64_t fd, int64_t enabled) {
    int val = enabled ? 1 : 0;
    return setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &val, sizeof(val)) == 0;
}
int64_t rt_io_tcp_set_nonblocking(int64_t fd, int64_t enabled) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (enabled) flags |= O_NONBLOCK; else flags &= ~O_NONBLOCK;
    return fcntl(fd, F_SETFL, flags) == 0;
}
int64_t rt_io_tcp_set_nodelay(int64_t fd, int64_t enabled) {
    int val = enabled ? 1 : 0;
    return setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &val, sizeof(val)) == 0;
}
int64_t rt_io_tcp_bind_fd(int64_t fd, const char* addr_str) {
    char buf[256];
    strncpy(buf, addr_str, sizeof(buf) - 1); buf[sizeof(buf)-1] = 0;
    char* colon = strrchr(buf, ':');
    if (!colon) return 0;
    *colon = 0;
    int port = atoi(colon + 1);
    struct sockaddr_in sa = {0};
    sa.sin_family = AF_INET;
    sa.sin_port = htons(port);
    inet_aton(buf, &sa.sin_addr);
    return bind(fd, (struct sockaddr*)&sa, sizeof(sa)) == 0;
}
int64_t rt_io_tcp_listen(int64_t fd, int64_t backlog) {
    return listen(fd, backlog) == 0;
}
int64_t rt_io_tcp_accept(int64_t fd) {
    return (int64_t)accept(fd, NULL, NULL);
}

RtVal rt_io_tcp_read(int64_t fd, int64_t size) {
    RuntimeArray* a = make_array(size, 1);  /* byte array */
    char* tmp = malloc(size);
    ssize_t n = read(fd, tmp, size);
    if (n > 0) {
        for (ssize_t i = 0; i < n; i++)
            a->data[i] = MAKE_INT((uint8_t)tmp[i]);
        a->len = n;
    }
    free(tmp);
    return array_to_val(a);
}

int64_t rt_io_tcp_write_text(int64_t fd, const char* data) {
    if (!data) return 0;
    size_t len = strlen(data);
    return (int64_t)write(fd, data, len);
}
int64_t rt_io_tcp_close(int64_t fd) { return close(fd) == 0; }

/* === Epoll === */
int64_t rt_event_loop_create(void) { return (int64_t)epoll_create1(0); }

int64_t rt_event_loop_register(int64_t epfd, int64_t fd, int64_t interest, int64_t token, int64_t edge) {
    struct epoll_event ev = {0};
    ev.events = EPOLLIN;
    if (interest == 1 || interest == 2) ev.events |= EPOLLOUT;
    if (edge) ev.events |= EPOLLET;
    ev.data.fd = fd;
    int r = epoll_ctl(epfd, EPOLL_CTL_ADD, fd, &ev);
    if (r < 0 && errno == EEXIST) r = epoll_ctl(epfd, EPOLL_CTL_MOD, fd, &ev);
    return r == 0;
}

static struct epoll_event poll_events[1024];

RtVal rt_event_loop_poll(int64_t epfd, int64_t max_events, int64_t timeout_ms) {
    if (max_events > 1024) max_events = 1024;
    int n = epoll_wait(epfd, poll_events, max_events, timeout_ms);
    RuntimeArray* a = make_array(n > 0 ? n : 1, 0);  /* i64 array, NOT byte packed */
    if (n > 0) {
        a->len = n;
        for (int i = 0; i < n; i++)
            a->data[i] = MAKE_INT(poll_events[i].data.fd);
    }
    return array_to_val(a);
}
