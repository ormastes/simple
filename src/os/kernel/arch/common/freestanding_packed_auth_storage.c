#include "freestanding_packed_auth_storage.h"

typedef struct {
    uint32_t occupied;
    uint32_t generation;
    _Alignas(16) uint8_t bytes[SIMPLEOS_PACKED_AUTH_X86_TOKEN_BYTES];
} SimpleOsPackedAuthSlot;

static SimpleOsPackedAuthSlot secret_slots[SIMPLEOS_PACKED_AUTH_STORAGE_SLOTS];
static SimpleOsPackedAuthSlot message_slots[SIMPLEOS_PACKED_AUTH_STORAGE_SLOTS];
static SimpleOsPackedAuthSlot token_slots[SIMPLEOS_PACKED_AUTH_STORAGE_SLOTS];
static volatile uint32_t packed_auth_lock;

static void packed_lock(void) {
    while (__atomic_exchange_n(&packed_auth_lock, 1U, __ATOMIC_ACQUIRE) != 0U) {}
}

static void packed_unlock(void) {
    __atomic_store_n(&packed_auth_lock, 0U, __ATOMIC_RELEASE);
}

static uint32_t packed_size(uint32_t kind) {
    if (kind == SIMPLEOS_PACKED_AUTH_SECRET) return SIMPLEOS_PACKED_AUTH_SECRET_BYTES;
    if (kind == SIMPLEOS_PACKED_AUTH_MESSAGE) return SIMPLEOS_PACKED_AUTH_MESSAGE_BYTES;
    if (kind == SIMPLEOS_PACKED_AUTH_X86_TOKEN) return SIMPLEOS_PACKED_AUTH_X86_TOKEN_BYTES;
    return 0U;
}

static SimpleOsPackedAuthSlot *packed_slots(uint32_t kind) {
    if (kind == SIMPLEOS_PACKED_AUTH_SECRET) return secret_slots;
    if (kind == SIMPLEOS_PACKED_AUTH_MESSAGE) return message_slots;
    if (kind == SIMPLEOS_PACKED_AUTH_X86_TOKEN) return token_slots;
    return (SimpleOsPackedAuthSlot *)0;
}

static void packed_wipe(uint8_t *bytes, uint32_t len) {
    volatile uint8_t *cursor = (volatile uint8_t *)bytes;
    uint32_t i;
    for (i = 0U; i < len; ++i) cursor[i] = 0U;
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
}

static SimpleOsPackedAuthSlot *packed_validate(SimpleOsPackedAuthLease lease) {
    SimpleOsPackedAuthSlot *slots = packed_slots(lease.kind);
    if (slots == (SimpleOsPackedAuthSlot *)0 ||
        lease.slot >= SIMPLEOS_PACKED_AUTH_STORAGE_SLOTS ||
        lease.generation == 0U) return (SimpleOsPackedAuthSlot *)0;
    if (slots[lease.slot].occupied == 0U ||
        slots[lease.slot].generation != lease.generation) {
        return (SimpleOsPackedAuthSlot *)0;
    }
    return &slots[lease.slot];
}

int32_t simpleos_packed_auth_claim(uint32_t kind,
                                   SimpleOsPackedAuthLease *lease_out) {
    SimpleOsPackedAuthSlot *slots = packed_slots(kind);
    uint32_t size = packed_size(kind);
    uint32_t i;
    if (slots == (SimpleOsPackedAuthSlot *)0 || size == 0U || lease_out == 0) return -22;
    packed_lock();
    for (i = 0U; i < SIMPLEOS_PACKED_AUTH_STORAGE_SLOTS; ++i) {
        if (slots[i].occupied == 0U) {
            uint32_t generation = slots[i].generation + 1U;
            if (generation == 0U) generation = 1U;
            packed_wipe(slots[i].bytes, size);
            slots[i].generation = generation;
            slots[i].occupied = 1U;
            lease_out->kind = kind;
            lease_out->slot = i;
            lease_out->generation = generation;
            packed_unlock();
            return 0;
        }
    }
    packed_unlock();
    return -28;
}

int32_t simpleos_packed_auth_write(SimpleOsPackedAuthLease lease,
                                   const uint8_t *source,
                                   uint32_t source_len) {
    uint32_t size = packed_size(lease.kind);
    uint32_t i;
    if (source == 0 || source_len != size || size == 0U) return -22;
    packed_lock();
    SimpleOsPackedAuthSlot *slot = packed_validate(lease);
    if (slot == (SimpleOsPackedAuthSlot *)0) { packed_unlock(); return -13; }
    for (i = 0U; i < size; ++i) slot->bytes[i] = source[i];
    packed_unlock();
    return 0;
}

int32_t simpleos_packed_auth_read(SimpleOsPackedAuthLease lease,
                                  uint8_t *destination,
                                  uint32_t destination_len) {
    uint32_t size = packed_size(lease.kind);
    uint32_t i;
    if (destination == 0 || destination_len != size || size == 0U) return -22;
    packed_lock();
    SimpleOsPackedAuthSlot *slot = packed_validate(lease);
    if (slot == (SimpleOsPackedAuthSlot *)0) { packed_unlock(); return -13; }
    for (i = 0U; i < size; ++i) destination[i] = slot->bytes[i];
    packed_unlock();
    return 0;
}

uintptr_t simpleos_packed_auth_address(SimpleOsPackedAuthLease lease) {
    uintptr_t result = 0U;
    packed_lock();
    SimpleOsPackedAuthSlot *slot = packed_validate(lease);
    if (slot != (SimpleOsPackedAuthSlot *)0) result = (uintptr_t)&slot->bytes[0];
    packed_unlock();
    return result;
}

int32_t simpleos_packed_auth_release(SimpleOsPackedAuthLease lease) {
    uint32_t size = packed_size(lease.kind);
    packed_lock();
    SimpleOsPackedAuthSlot *slot = packed_validate(lease);
    if (slot == (SimpleOsPackedAuthSlot *)0) { packed_unlock(); return -13; }
    packed_wipe(slot->bytes, size);
    slot->occupied = 0U;
    packed_unlock();
    return 0;
}

static uint64_t packed_lease_encode(SimpleOsPackedAuthLease lease) {
    return ((uint64_t)lease.generation << 16U) |
           ((uint64_t)(lease.slot & 0xffU) << 8U) |
           (uint64_t)(lease.kind & 0xffU);
}

static SimpleOsPackedAuthLease packed_lease_decode(uint64_t encoded) {
    SimpleOsPackedAuthLease lease;
    lease.kind = (uint32_t)(encoded & 0xffU);
    lease.slot = (uint32_t)((encoded >> 8U) & 0xffU);
    lease.generation = (uint32_t)(encoded >> 16U);
    return lease;
}

uint64_t rt_packed_auth_claim(uint32_t kind) {
    SimpleOsPackedAuthLease lease;
    if (simpleos_packed_auth_claim(kind, &lease) != 0) return 0U;
    return packed_lease_encode(lease);
}

int32_t rt_packed_auth_write_byte(uint64_t encoded, uint32_t index, uint32_t value) {
    SimpleOsPackedAuthLease lease = packed_lease_decode(encoded);
    uint32_t size = packed_size(lease.kind);
    if (index >= size || value > 255U || size == 0U) return -22;
    packed_lock();
    SimpleOsPackedAuthSlot *slot = packed_validate(lease);
    if (slot == (SimpleOsPackedAuthSlot *)0) { packed_unlock(); return -13; }
    slot->bytes[index] = (uint8_t)value;
    packed_unlock();
    return 0;
}

uint64_t rt_packed_auth_address(uint64_t encoded) {
    return (uint64_t)simpleos_packed_auth_address(packed_lease_decode(encoded));
}

int32_t rt_packed_auth_release(uint64_t encoded) {
    return simpleos_packed_auth_release(packed_lease_decode(encoded));
}
