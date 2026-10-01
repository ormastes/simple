#include <stdint.h>
#include <stdio.h>

static uint64_t pmm_base;
static uint64_t pmm_limit;
static uint64_t pmm_next;
static uint64_t pmm_free_pages;
static uint64_t pmm_total_pages;
static int pmm_ready;
static uint64_t normalize_phys32(uint64_t value) {
    if ((value >> 32) == UINT64_C(0xffffffff)) {
        return value & UINT64_C(0xffffffff);
    }
    return value;
}

static void reset_pmm(void) {
    pmm_base = 0;
    pmm_limit = 0;
    pmm_next = 0;
    pmm_free_pages = 0;
    pmm_total_pages = 0;
    pmm_ready = 0;
}

static int init_pmm(uint64_t ram_base, uint64_t ram_size, uint64_t reserved_end, uint64_t heap_start) {
    const uint64_t page_size = UINT64_C(4096);
    uint64_t ram_end;
    uint64_t alloc_base;
    ram_base = normalize_phys32(ram_base);
    reserved_end = normalize_phys32(reserved_end);
    heap_start = normalize_phys32(heap_start);
    if (ram_size <= page_size) return 0;
    if (reserved_end <= ram_base) return 0;
    if (heap_start <= reserved_end) return 0;
    ram_end = ram_base + ram_size;
    if (ram_end <= ram_base) return 0;
    if (heap_start > ram_end) return 0;
    alloc_base = (reserved_end + page_size - UINT64_C(1)) & ~(page_size - UINT64_C(1));
    if (alloc_base >= heap_start) return 0;
    pmm_base = alloc_base;
    pmm_limit = heap_start;
    pmm_next = alloc_base;
    pmm_total_pages = (heap_start - alloc_base) / page_size;
    pmm_free_pages = pmm_total_pages;
    pmm_ready = 1;
    return 1;
}

static uint64_t alloc_page(void) {
    uint64_t page;
    if (!pmm_ready) return 0;
    if (pmm_next >= pmm_limit) return 0;
    page = pmm_next;
    pmm_next += UINT64_C(4096);
    if (pmm_free_pages > 0) pmm_free_pages--;
    return page;
}

static void emit(const char *case_id, int ok, uint64_t page0, uint64_t page1, uint64_t page2) {
    printf("%s ok=%d ready=%d base=%llu limit=%llu next=%llu total=%llu free=%llu pages=%llu,%llu,%llu\n",
           case_id, ok, pmm_ready,
           (unsigned long long)pmm_base, (unsigned long long)pmm_limit,
           (unsigned long long)pmm_next, (unsigned long long)pmm_total_pages,
           (unsigned long long)pmm_free_pages, (unsigned long long)page0,
           (unsigned long long)page1, (unsigned long long)page2);
}

int main(void) {
    int ok;
    uint64_t page0, page1, page2;

    reset_pmm();
    ok = init_pmm(UINT64_C(0x80000000), UINT64_C(4096), UINT64_C(0x80200000), UINT64_C(0x80400000));
    emit("invalid-small", ok, alloc_page(), 0, 0);

    reset_pmm();
    ok = init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80200001), UINT64_C(0x80203000));
    page0 = alloc_page(); page1 = alloc_page(); page2 = alloc_page();
    emit("alignment-exhaustion", ok, page0, page1, page2);

    reset_pmm();
    ok = init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80200000), UINT64_C(0x80200001));
    page0 = alloc_page();
    emit("short-window", ok, page0, 0, 0);

    reset_pmm();
    ok = init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80200000), UINT64_C(0x80203000));
    page0 = alloc_page();
    ok = ok && init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80300000), UINT64_C(0x80302000));
    emit("valid-reset", ok, page0, 0, 0);

    reset_pmm();
    ok = init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80200000), UINT64_C(0x80202000));
    page0 = alloc_page();
    ok = ok && !init_pmm(UINT64_C(0x80000000), UINT64_C(4096), UINT64_C(0x80200000), UINT64_C(0x80202000));
    emit("invalid-retains-state", ok, page0, 0, 0);

    reset_pmm();
    ok = init_pmm(UINT64_C(0xffffffff80000000), UINT64_C(0x08000000), UINT64_C(0xffffffff80200001), UINT64_C(0xffffffff80203000));
    page0 = alloc_page();
    emit("sign-extended", ok, page0, 0, 0);

    reset_pmm();
    ok = init_pmm(UINT64_C(0xfffffffefffff000), UINT64_C(0x100002000), UINT64_C(0xfffffffefffff100), UINT64_C(0xfffffffefffff800));
    emit("ram-end-wrap", ok, alloc_page(), 0, 0);

    reset_pmm();
    ok = !init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80000000), UINT64_C(0x80400000));
    ok = ok && !init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80200000), UINT64_C(0x80200000));
    ok = ok && !init_pmm(UINT64_C(0x80000000), UINT64_C(0x01000000), UINT64_C(0x80200000), UINT64_C(0x82000000));
    ok = ok && !init_pmm(UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80200001), UINT64_C(0x80201000));
    emit("remaining-invalid", ok, 0, 0, 0);

    return 0;
}
