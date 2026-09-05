#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <pthread.h>

static pthread_key_t owner_key;
static bool admitted;
static int64_t address;
static uint8_t value;
static int capability;
static bool cross_thread_rejected;

extern int64_t rt_hosted_volatile_u8_admit(void);
extern int64_t rt_hosted_volatile_u8_owned(void);

static bool current_owner(void) {
    return admitted && pthread_getspecific(owner_key) == &capability;
}

static bool admit(void) {
    if (admitted) return false;
    if (pthread_key_create(&owner_key, NULL) != 0) return false;
    if (pthread_setspecific(owner_key, &capability) != 0) return false;
    admitted = true;
    return true;
}

static bool register_u8(int64_t addr, int64_t initial) {
    if (!current_owner() || addr <= 0 || address != 0) return false;
    address = addr;
    value = (uint8_t)initial;
    return true;
}

static int64_t read_u8(int64_t addr) {
    if (!current_owner() || addr != address) return -1;
    return value;
}

static void write_u8(int64_t addr, int64_t next) {
    if (!current_owner() || addr != address) return;
    value = (uint8_t)next;
}

static void *cross_thread_probe(void *unused) {
    (void)unused;
    int64_t before = value;
    write_u8(4096, 77);
    cross_thread_rejected = !current_owner() && !register_u8(8192, 1) &&
        read_u8(4096) == -1 && value == before &&
        rt_hosted_volatile_u8_owned() == 0 &&
        rt_hosted_volatile_u8_admit() == 0;
    return NULL;
}

int main(void) {
    if (rt_hosted_volatile_u8_owned() != 0 || rt_hosted_volatile_u8_admit() != 1 ||
        rt_hosted_volatile_u8_owned() != 1) return 1;
    if (!admit()) return 2;
    if (!register_u8(4096, 0)) return 3;
    pthread_t probe;
    if (pthread_create(&probe, NULL, cross_thread_probe, NULL) != 0) return 4;
    if (pthread_join(probe, NULL) != 0 || !cross_thread_rejected) return 5;
    int64_t checksum = 0;
    for (int64_t i = 0; i < 2000000; ++i) {
        write_u8(4096, i);
        checksum += read_u8(4096);
    }
    printf("%lld\n", (long long)checksum);
    return 0;
}
