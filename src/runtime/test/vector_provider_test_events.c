/* Bounded LD_PRELOAD receipt owner for test-only vector provider events. */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#define RECEIPT_FD 3
#define RECEIPT_CAPACITY 4096
#define STATUS_COUNT 7

static pid_t receipt_owner_pid;
static int receipt_owner;
static atomic_uint_fast64_t load_count;
static atomic_uint_fast64_t event_count;
static atomic_uint_fast64_t events_by_opcode_status[5][STATUS_COUNT];
static atomic_uint_fast64_t loops_by_opcode[5];
static atomic_uint_fast64_t malformed_count;
static atomic_int overflow_seen;

static void add_saturating(atomic_uint_fast64_t *counter, uint64_t amount) {
    uint_fast64_t old = atomic_load_explicit(counter, memory_order_relaxed);
    for (;;) {
        if (amount > UINT64_MAX - old) {
            atomic_store_explicit(&overflow_seen, 1, memory_order_relaxed);
            return;
        }
        if (atomic_compare_exchange_weak_explicit(
                counter, &old, old + amount,
                memory_order_relaxed, memory_order_relaxed))
            return;
    }
}

__attribute__((visibility("default")))
void simple_vector_test_loaded(void) {
    if (!receipt_owner || getpid() != receipt_owner_pid) return;
    add_saturating(&load_count, 1);
}

__attribute__((visibility("default")))
void simple_vector_test_apply_event_v1(uint32_t opcode, uint32_t status,
        uint64_t executed_loops) {
    if (!receipt_owner || getpid() != receipt_owner_pid) return;
    add_saturating(&event_count, 1);
    if (opcode < 1 || opcode > 4 || status >= STATUS_COUNT) {
        add_saturating(&malformed_count, 1);
        return;
    }
    add_saturating(&events_by_opcode_status[opcode][status], 1);
    if (status == 0) {
        add_saturating(&loops_by_opcode[opcode], executed_loops);
    } else if (executed_loops != 0) {
        add_saturating(&malformed_count, 1);
    }
}

__attribute__((constructor)) static void claim_receipt_owner(void) {
    receipt_owner_pid = getpid();
    const char *owner = getenv("SIMPLE_VECTOR_TEST_RECEIPT_OWNER");
    receipt_owner = owner && strcmp(owner, "1") == 0;
    unsetenv("SIMPLE_VECTOR_TEST_RECEIPT_OWNER");
}

static size_t append(char *buffer, size_t used, const char *format, ...) {
    if (used >= RECEIPT_CAPACITY) {
        atomic_store_explicit(&overflow_seen, 1, memory_order_relaxed);
        return used;
    }
    va_list args;
    va_start(args, format);
    int wrote = vsnprintf(buffer + used, RECEIPT_CAPACITY - used, format, args);
    va_end(args);
    if (wrote < 0 || (size_t)wrote >= RECEIPT_CAPACITY - used) {
        atomic_store_explicit(&overflow_seen, 1, memory_order_relaxed);
        return RECEIPT_CAPACITY;
    }
    return used + (size_t)wrote;
}

static int write_all(int fd, const char *buffer, size_t length) {
    size_t offset = 0;
    while (offset < length) {
        ssize_t wrote = write(fd, buffer + offset, length - offset);
        if (wrote < 0 && errno == EINTR) continue;
        if (wrote <= 0) return 0;
        offset += (size_t)wrote;
    }
    return 1;
}

__attribute__((destructor)) static void write_receipt(void) {
    if (!receipt_owner || getpid() != receipt_owner_pid) return;
    char buffer[RECEIPT_CAPACITY];
    size_t used = 0;
    used = append(buffer, used, "SIMPLE_VECTOR_TEST_EVENTS_V1\n");
    used = append(buffer, used, "pid=%ld\n", (long)getpid());
    used = append(buffer, used, "loads=%llu\n",
        (unsigned long long)atomic_load_explicit(&load_count, memory_order_relaxed));
    used = append(buffer, used, "events=%llu\n",
        (unsigned long long)atomic_load_explicit(&event_count, memory_order_relaxed));
    used = append(buffer, used, "malformed=%llu\n",
        (unsigned long long)atomic_load_explicit(&malformed_count, memory_order_relaxed));
    used = append(buffer, used, "overflow=%d\n",
        atomic_load_explicit(&overflow_seen, memory_order_relaxed));
    for (uint32_t opcode = 1; opcode <= 4; ++opcode) {
        used = append(buffer, used, "op%u_loops=%llu\n", opcode,
            (unsigned long long)atomic_load_explicit(
                &loops_by_opcode[opcode], memory_order_relaxed));
        for (uint32_t status = 0; status < STATUS_COUNT; ++status) {
            used = append(buffer, used, "op%u_status%u=%llu\n", opcode, status,
                (unsigned long long)atomic_load_explicit(
                    &events_by_opcode_status[opcode][status], memory_order_relaxed));
        }
    }
    if (used >= RECEIPT_CAPACITY || !write_all(RECEIPT_FD, buffer, used))
        _exit(74);
}
