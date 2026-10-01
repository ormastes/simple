#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <pthread.h>

static pthread_key_t owner_key;
static bool admitted;
static int64_t address;
static uint16_t value;
static int capability;

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

static bool register_u16(int64_t addr, int64_t initial) {
    if (!current_owner() || addr <= 0 || address != 0) return false;
    address = addr;
    value = (uint16_t)initial;
    return true;
}

static int64_t read_u16(int64_t addr) {
    if (!current_owner() || addr != address) return -1;
    return value;
}

static void write_u16(int64_t addr, int64_t next) {
    if (!current_owner() || addr != address) return;
    value = (uint16_t)next;
}

int main(void) {
    if (!admit()) return 2;
    if (!register_u16(4096, 0)) return 3;
    int64_t checksum = 0;
    for (int64_t i = 0; i < 2000000; ++i) {
        write_u16(4096, i);
        checksum += read_u16(4096);
    }
    printf("%lld\n", (long long)checksum);
    return 0;
}
