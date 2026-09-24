#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

static _Atomic uint64_t kpf_total_allocations;
static _Atomic uint64_t kpf_activation_total;
static _Atomic int kpf_active;

void kpf_noalloc_probe_activate(void) {
    atomic_store_explicit(&kpf_activation_total,
                          atomic_load_explicit(&kpf_total_allocations, memory_order_relaxed),
                          memory_order_relaxed);
    atomic_store_explicit(&kpf_active, 1, memory_order_release);
}

uint64_t kpf_noalloc_probe_post_activation_allocations(void) {
    uint64_t total = atomic_load_explicit(&kpf_total_allocations, memory_order_relaxed);
    uint64_t baseline = atomic_load_explicit(&kpf_activation_total, memory_order_relaxed);
    return total - baseline;
}

static void kpf_record_allocation(void) {
    atomic_fetch_add_explicit(&kpf_total_allocations, 1, memory_order_relaxed);
}

#if defined(__APPLE__)

#include <malloc/malloc.h>

static void *kpf_probe_malloc(size_t size) {
    kpf_record_allocation();
    return malloc_zone_malloc(malloc_default_zone(), size);
}

static void *kpf_probe_calloc(size_t count, size_t size) {
    kpf_record_allocation();
    return malloc_zone_calloc(malloc_default_zone(), count, size);
}

static void *kpf_probe_realloc(void *pointer, size_t size) {
    kpf_record_allocation();
    return malloc_zone_realloc(malloc_default_zone(), pointer, size);
}

#define KPF_DYLD_INTERPOSE(replacement, replacee) \
    __attribute__((used)) static struct { const void *replacement; const void *replacee; } \
    kpf_interpose_##replacee __attribute__((section("__DATA,__interpose"))) = { \
        (const void *)(uintptr_t)&replacement, (const void *)(uintptr_t)&replacee \
    }

KPF_DYLD_INTERPOSE(kpf_probe_malloc, malloc);
KPF_DYLD_INTERPOSE(kpf_probe_calloc, calloc);
KPF_DYLD_INTERPOSE(kpf_probe_realloc, realloc);

#else

void *__real_malloc(size_t size);
void *__real_calloc(size_t count, size_t size);
void *__real_realloc(void *pointer, size_t size);

void *__wrap_malloc(size_t size) {
    kpf_record_allocation();
    return __real_malloc(size);
}

void *__wrap_calloc(size_t count, size_t size) {
    kpf_record_allocation();
    return __real_calloc(count, size);
}

void *__wrap_realloc(void *pointer, size_t size) {
    kpf_record_allocation();
    return __real_realloc(pointer, size);
}

#endif
