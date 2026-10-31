/* Run from the repository root (macOS):
 * cc -std=c11 -O0 -Wall -Wextra -Werror -pthread src/runtime/test/runtime_process_darwin_pin_selfcheck.c src/runtime/runtime_process_tree.c -o /tmp/pov4-darwin-pin
 * /tmp/pov4-darwin-pin
 *
 * The real Darwin executable pin (runtime_process_owned.c): a private
 * snapshot that is digested, re-validated on every acquisition, refused after
 * a mode change or a pathname substitution, released completely, and usable
 * by the observation V4 owner end to end. */
#if !defined(__APPLE__)
#include <stdio.h>
int main(void) { puts("runtime_process_darwin_pin_selfcheck: SKIP (requires macOS)"); return 77; }
#else
#define _DARWIN_C_SOURCE
#include "../runtime.h"
#include <assert.h>
#include <CommonCrypto/CommonDigest.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <mach-o/dyld.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

SplArray* rt_array_new(int64_t capacity) {
    SplArray* a = calloc(1, sizeof(*a)); assert(a);
    a->cap = capacity > 0 ? capacity : 1;
    a->items = calloc((size_t)a->cap, sizeof(*a->items)); assert(a->items);
    return a;
}
int64_t rt_array_len(SplArray* a) { return a ? a->len : -1; }
int64_t rt_array_get(SplArray* a, int64_t i) {
    return a && i >= 0 && i < a->len ? a->items[i].as_int : 0;
}
int8_t rt_array_push(SplArray* a, int64_t value) {
    if (!a || a->len >= a->cap) return 0;
    a->items[a->len++].as_int = value; return 1;
}
int8_t rt_array_set(SplArray* a, int64_t i, int64_t value) {
    if (!a || i < 0 || i >= a->len) return 0;
    a->items[i].as_int = value; return 1;
}
int64_t rt_value_int(int64_t value) { return value; }
int64_t rt_value_as_int(int64_t value) { return value; }
int8_t rt_value_is_int(int64_t value) { (void)value; return 1; }
void* rt_alloc(int64_t size) { return size > 0 ? calloc(1, (size_t)size) : NULL; }
void rt_free(void* value) { free(value); }
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t* rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_new(const uint8_t* bytes, uint64_t length) { (void)bytes; (void)length; return 1; }
void rt_array_free(SplArray* a) { if (a) { free(a->items); free(a); } }
int64_t rt_tuple_new(int64_t len) {
    SplArray* a = rt_array_new(len);
    for (int64_t i = 0; i < len; i++) assert(rt_array_push(a, 0));
    return (int64_t)(uintptr_t)a;
}
int8_t rt_tuple_set(int64_t tuple, int64_t index, int64_t value) {
    return rt_array_set((SplArray*)(uintptr_t)tuple, index, value);
}
int64_t rt_free_deep(int64_t value) { (void)value; return 1; }
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* a = (SplArray*)(uintptr_t)value;
    if (!a) return -1;
    for (int64_t i = 0; i < a->len; i++)
        if (rt_array_get(a, i) < 0 || rt_array_get(a, i) > 255) return -1;
    return a->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t cap) {
    int64_t n = rt_array_bytes_validate(value); if (n < 0 || n > cap) return -1;
    SplArray* a = (SplArray*)(uintptr_t)value;
    for (int64_t i = 0; i < n; i++) out[i] = (uint8_t)rt_array_get(a, i);
    return n;
}

#include "../runtime_process_owned.c"

static uint8_t self_digest[32];
static void hash_path(const char* path, uint8_t digest[32]) {
    int fd = open(path, O_RDONLY | O_CLOEXEC); assert(fd >= 0);
    assert(pov4_darwin_hash_fd(fd, digest)); assert(close(fd) == 0);
}
static int open_fd_count(void) {
    int count = 0;
    for (int fd = 0; fd < 4096; fd++) if (fcntl(fd, F_GETFD) >= 0) count++;
    return count;
}
static const OwnedDarwinPin* find_pin(int64_t handle) {
    for (int i = 0; i < OWNED_DARWIN_PIN_SLOTS; i++)
        if (owned_darwin_pins[i].handle == (uint64_t)handle) return &owned_darwin_pins[i];
    return NULL;
}
static int digest_equals(SplArray* digest, const uint8_t expected[32]) {
    if (!digest || rt_array_len(digest) != 32) return 0;
    for (int i = 0; i < 32; i++) if (rt_array_get(digest, i) != expected[i]) return 0;
    return 1;
}
static void put_u64(SplArray* a, uint64_t value) {
    for (int i = 0; i < 8; i++) assert(rt_array_push(a, (int64_t)((value >> (8 * i)) & 255)));
}
static void set_u64_at(SplArray* a, int64_t offset, uint64_t value) {
    for (int i = 0; i < 8; i++) assert(rt_array_set(a, offset + i, (int64_t)((value >> (8 * i)) & 255)));
}
static void put_bytes(SplArray* a, const uint8_t* bytes, size_t n) {
    for (size_t i = 0; i < n; i++) assert(rt_array_push(a, bytes[i]));
}
static void put_text(SplArray* a, const char* text) {
    size_t n = strlen(text); put_u64(a, n); put_bytes(a, (const uint8_t*)text, n);
}
/* Offsets: 24 wall, 32 grace, 40 cleanup, 64 memory, 72 enforcement, 80 policy. */
static SplArray* request_bytes(const char* cwd, int64_t cwd_pin, const uint8_t cwd_digest[32],
                               const char* child_arg, uint64_t policy) {
    SplArray* a = rt_array_new(2048);
    const uint8_t magic[8] = {'P','O','V','4','R','E','Q',0}; put_bytes(a, magic, 8);
    put_u64(a, 1); put_u64(a, POV4_DARWIN_CAPABILITIES); put_u64(a, 5000000000ULL);
    put_u64(a, 100000000ULL); put_u64(a, 2000000000ULL);
    put_u64(a, 4096); put_u64(a, 4096); put_u64(a, 0);
    put_u64(a, POV4_ENFORCEMENT_NONE); put_u64(a, policy); put_u64(a, 10000000); put_u64(a, 0);
    put_bytes(a, self_digest, 32); put_text(a, cwd); put_text(a, cwd);
    put_u64(a, (uint64_t)cwd_pin); put_bytes(a, cwd_digest, 32);
    put_u64(a, 2); put_text(a, "pov4-darwin-live"); put_text(a, child_arg);
    put_u64(a, 1); put_text(a, "POV4_TEST"); put_text(a, "exact");
    return a;
}
static SplArray* tuple_item(SplArray* tuple, int index) {
    return (SplArray*)(uintptr_t)rt_array_get(tuple, index);
}
static int64_t word(SplArray* tuple, int index) { return rt_array_get(tuple_item(tuple, 3), index); }
static SplArray* ticket_from(SplArray* tuple) {
    SplArray* t = rt_array_new(5);
    assert(rt_array_push(t, 4));
    for (int i = 4; i <= 7; i++) assert(rt_array_push(t, word(tuple, i)));
    return t;
}
static SplArray* collect_until(SplArray* ticket, int64_t kind) {
    for (int turn = 0; turn < 400; turn++) {
        SplArray* result = rt_process_observation_v4_collect_value(ticket, 25000000);
        if (word(result, POV4_PACKET_KIND) == kind) return result;
    }
    fprintf(stderr, "collect never reached packet kind %lld\n", (long long)kind);
    abort();
}

static void check_pin_lifecycle(const char* self) {
    int baseline = open_fd_count();
    assert(rt_process_pin_executable_owned("relative/path") == -1);
    assert(rt_process_pin_executable_owned_value((const uint8_t*)"/x\0y", 4) == -1);
    char text_file[] = "/tmp/pov4-pin-text-XXXXXX";
    int t = mkstemp(text_file); assert(t >= 0);
    assert(write(t, "#!/bin/sh\n", 10) == 10 && fchmod(t, 0700) == 0 && close(t) == 0);
    assert(rt_process_pin_executable_owned(text_file) == -1); /* Not Mach-O. */
    assert(unlink(text_file) == 0);

    int64_t pin = rt_process_pin_executable_owned_value((const uint8_t*)self, strlen(self));
    assert(pin > 0);
    const OwnedDarwinPin* record = find_pin(pin); assert(record);
    char directory[PATH_MAX], path[PATH_MAX];
    strcpy(directory, record->directory); strcpy(path, record->path);
    struct stat st;
    assert(stat(directory, &st) == 0 && (st.st_mode & 07777) == 0700);
    assert(stat(path, &st) == 0 && (st.st_mode & 07777) == 0500 && st.st_uid == geteuid());
    assert(digest_equals(rt_process_pinned_executable_sha256_value(pin), self_digest));
    int fd = (int)rt_process_acquire_pinned_executable(pin);
    assert(fd >= 3 && (fcntl(fd, F_GETFD) & FD_CLOEXEC) && close(fd) == 0);
    assert(rt_process_acquire_pinned_executable(pin + 1) == -1);

    /* A writable snapshot is no longer a pin. */
    assert(chmod(path, 0700) == 0);
    errno = 0;
    assert(rt_process_acquire_pinned_executable(pin) == -1 && errno == ESTALE);
    assert(rt_process_pinned_executable_sha256_value(pin) == NULL);
    assert(chmod(path, 0500) == 0);
    fd = (int)rt_process_acquire_pinned_executable(pin); assert(fd >= 0 && close(fd) == 0);

    /* Substituting the pathname (same bytes, new inode) is refused. */
    char moved[PATH_MAX]; assert(snprintf(moved, sizeof(moved), "%s.moved", path) > 0);
    assert(rename(path, moved) == 0);
    int copy = open(path, O_WRONLY | O_CREAT | O_EXCL, 0500); assert(copy >= 0); assert(close(copy) == 0);
    errno = 0;
    assert(rt_process_acquire_pinned_executable(pin) == -1 && errno == ESTALE);
    assert(unlink(path) == 0 && rename(moved, path) == 0);

    assert(rt_process_close_pinned_executable_owned_value(pin) == 1);
    assert(rt_process_close_pinned_executable_owned_value(pin) == 0);
    assert(rt_process_acquire_pinned_executable(pin) == -1);
    assert(stat(path, &st) != 0 && stat(directory, &st) != 0);
    assert(open_fd_count() == baseline);

    /* The table is bounded; a full table refuses instead of overwriting. */
    int64_t pins[OWNED_DARWIN_PIN_SLOTS];
    for (int i = 0; i < OWNED_DARWIN_PIN_SLOTS; i++) {
        pins[i] = rt_process_pin_executable_owned(self); assert(pins[i] > 0);
    }
    assert(rt_process_pin_executable_owned(self) == -1);
    for (int i = 0; i < OWNED_DARWIN_PIN_SLOTS; i++)
        assert(rt_process_close_pinned_executable_owned(pins[i]));
    assert(open_fd_count() == baseline);
}

static void check_owner_with_real_pin(const char* self) {
    int64_t pin = rt_process_pin_executable_owned(self); assert(pin > 0);
    char cwd[PATH_MAX]; assert(realpath(".", cwd));
    int64_t cwd_pin = rt_process_observation_v4_pin_cwd_value(cwd, strlen(cwd)); assert(cwd_pin > 0);
    SplArray* cwd_digest_value = rt_process_observation_v4_cwd_digest_value(cwd_pin);
    uint8_t cwd_digest[32];
    assert(rt_array_bytes_copy_checked((int64_t)(uintptr_t)cwd_digest_value, cwd_digest, 32) == 32);
    SplArray* request = request_bytes(cwd, cwd_pin, cwd_digest, "--slow-child", POV4_DESCENDANT_PROCESS_GROUP);
    set_u64_at(request, 96, (uint64_t)pin);
    const OwnedDarwinPin* record = find_pin(pin); assert(record);
    char directory[PATH_MAX]; strcpy(directory, record->directory);
    SplArray* started = rt_process_observation_v4_start_pinned_value(pin, cwd_pin, request);
    assert(word(started, POV4_STATUS) == POV4_STATUS_RUNNING);
    /* The owner closes its pin right after start (as the BuildRunner worker
     * does). The snapshot must outlive that while the child lives: AMFI
     * evaluates it after exec and kills a child whose image was unlinked. */
    assert(rt_process_close_pinned_executable_owned(pin));
    assert(rt_process_acquire_pinned_executable(pin) == -1);
    struct stat st; assert(stat(directory, &st) == 0);
    SplArray* ticket = ticket_from(started);
    SplArray* frozen = collect_until(ticket, POV4_KIND_FROZEN);
    assert(word(frozen, POV4_EXIT_CODE) == 7);
    assert(word(frozen, POV4_TREE_EMPTY) == 1 && word(frozen, POV4_LEADER_REAPED) == 1);
    assert(word(rt_process_observation_v4_ack_collect_value(ticket, tuple_item(frozen, 2)),
                POV4_PACKET_KIND) == POV4_KIND_ACK);
    assert(stat(directory, &st) != 0); /* Released with the collected lease. */
    assert(rt_process_observation_v4_close_cwd_value(cwd_pin) == 1);
    assert(!rt_process_close_pinned_executable_owned(pin));
}

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--slow-child") == 0) { usleep(300000); return 7; }
    char self[PATH_MAX]; uint32_t size = sizeof(self);
    assert(_NSGetExecutablePath(self, &size) == 0);
    char canonical[PATH_MAX]; assert(realpath(self, canonical));
    hash_path(canonical, self_digest);
    check_pin_lifecycle(canonical);
    check_owner_with_real_pin(canonical);
    puts("runtime_process_darwin_pin_selfcheck: PASS");
    return 0;
}
#endif
