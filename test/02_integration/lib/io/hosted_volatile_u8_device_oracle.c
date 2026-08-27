#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <pthread.h>

enum { CAPACITY = 64 };

struct legacy_owner {
    bool admitted;
    int64_t generation;
    int64_t addresses[CAPACITY];
    uint8_t values[CAPACITY];
    size_t count;
};

static struct legacy_owner owner;
static bool abi_cross_thread_rejected;

extern int64_t rt_hosted_volatile_u8_admit(void);
extern int64_t rt_hosted_volatile_u8_owned(void);

static void *abi_cross_thread_probe(void *unused) {
    (void)unused;
    abi_cross_thread_rejected = rt_hosted_volatile_u8_owned() == 0 &&
        rt_hosted_volatile_u8_admit() == 0;
    return NULL;
}

static bool legacy_owned(void) {
    return owner.admitted;
}

static bool legacy_admit(void) {
    if (owner.admitted) return false;
    memset(&owner, 0, sizeof owner);
    owner.admitted = true;
    owner.generation = 1;
    return true;
}

static bool legacy_reset(void) {
    if (!legacy_owned()) return false;
    owner.count = 0;
    owner.generation++;
    return true;
}

static bool legacy_register(int64_t addr, int64_t initial) {
    if (!legacy_owned()) return false;
    if (addr <= 0) return false;
    for (size_t i = 0; i < owner.count; ++i)
        if (owner.addresses[i] == addr) return false;
    if (owner.count >= CAPACITY) return false;
    owner.addresses[owner.count] = addr;
    owner.values[owner.count] = (uint8_t)initial;
    owner.count++;
    owner.generation++;
    return true;
}

static bool legacy_unregister(int64_t addr) {
    if (!legacy_owned()) return false;
    size_t found = CAPACITY;
    for (size_t i = 0; i < owner.count; ++i)
        if (owner.addresses[i] == addr) found = i;
    if (found == CAPACITY) return false;
    for (size_t i = found + 1; i < owner.count; ++i) {
        owner.addresses[i - 1] = owner.addresses[i];
        owner.values[i - 1] = owner.values[i];
    }
    owner.count--;
    owner.generation++;
    return true;
}

static int64_t legacy_read(int64_t addr) {
    if (!legacy_owned()) return -1;
    for (size_t i = 0; i < owner.count; ++i)
        if (owner.addresses[i] == addr) return owner.values[i];
    return -1;
}

static bool legacy_write(int64_t addr, int64_t value) {
    if (!legacy_owned()) return false;
    for (size_t i = 0; i < owner.count; ++i) {
        if (owner.addresses[i] == addr) {
            owner.values[i] = (uint8_t)value;
            owner.generation++;
            return true;
        }
    }
    return false;
}

static void emit_bool(const char *name, bool value) {
    printf("%s,%s\n", name, value ? "true" : "false");
}

static void emit_i64(const char *name, int64_t value) {
    printf("%s,%lld\n", name, (long long)value);
}

int main(void) {
    if (rt_hosted_volatile_u8_owned() != 0 || rt_hosted_volatile_u8_admit() != 1 ||
        rt_hosted_volatile_u8_owned() != 1) return 1;
    pthread_t abi_probe;
    bool abi_thread_started = pthread_create(&abi_probe, NULL, abi_cross_thread_probe, NULL) == 0;
    bool abi_thread_joined = abi_thread_started && pthread_join(abi_probe, NULL) == 0;
    if (!abi_thread_joined || !abi_cross_thread_rejected) return 2;
    emit_bool("owned-before-admit", legacy_owned());
    emit_i64("read-before-admit", legacy_read(4096));
    emit_bool("write-before-admit", legacy_write(4096, 1));
    emit_bool("admit-owner", legacy_admit());
    emit_bool("owned-after-admit", legacy_owned());
    emit_bool("admit-duplicate", legacy_admit());
    emit_i64("generation-admit", owner.generation);
    emit_bool("register-zero-address", legacy_register(0, 1));
    emit_bool("register-u8-a", legacy_register(4096, 511));
    emit_bool("register-duplicate", legacy_register(4096, 2));
    emit_bool("register-u8-b", legacy_register(12288, 17));
    emit_bool("register-u8-c", legacy_register(16384, 33));
    emit_i64("generation-register", owner.generation);
    emit_i64("facade-read-unknown", legacy_read(8192));
    emit_i64("facade-read-normalized", legacy_read(4096));
    legacy_write(8192, 1);
    emit_i64("generation-write-unknown", owner.generation);
    legacy_write(4096, 258);
    emit_i64("facade-read-written", legacy_read(4096));
    emit_i64("generation-write", owner.generation);
    emit_bool("unregister-unknown", legacy_unregister(8192));
    emit_i64("generation-unregister-unknown", owner.generation);
    emit_bool("unregister-middle", legacy_unregister(12288));
    emit_i64("retained-left", legacy_read(4096));
    emit_i64("removed-middle", legacy_read(12288));
    emit_i64("retained-right", legacy_read(16384));
    emit_i64("generation-unregister", owner.generation);
    emit_bool("reset-owner", legacy_reset());
    emit_i64("generation-reset", owner.generation);
    bool all_registered = true;
    for (int64_t i = 0; i < CAPACITY; ++i)
        if (!legacy_register(32768 + i, i)) all_registered = false;
    emit_bool("capacity-fill", all_registered);
    emit_bool("capacity-reject", legacy_register(65536, 1));
    emit_i64("capacity-live", (int64_t)owner.count);
    emit_i64("generation-capacity", owner.generation);
    return 0;
}
