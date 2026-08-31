#ifndef SIMPLEOS_FV_ALLOC
#error "SIMPLEOS_FV_ALLOC must name the target allocator"
#endif
#ifndef SIMPLEOS_FV_PANIC
#error "SIMPLEOS_FV_PANIC must name the non-returning target panic hook"
#endif

#include "freestanding_value_registry.h"

typedef struct { uintptr_t ptr; size_t bytes; } SimpleOsFvAllocation;
static SimpleOsFvAllocation simpleos_fv_structs[SIMPLEOS_FV_REGISTRY_CAP];
static SimpleOsFvAllocation simpleos_fv_enums[SIMPLEOS_FV_REGISTRY_CAP];
static size_t simpleos_fv_struct_count;
static size_t simpleos_fv_enum_count;
static uint8_t simpleos_fv_registry_lock;

static void simpleos_fv_lock(void)
{
    while (__atomic_test_and_set(&simpleos_fv_registry_lock, __ATOMIC_ACQUIRE)) {
        __asm__ volatile("" ::: "memory");
    }
}

static void simpleos_fv_unlock(void)
{
    __atomic_clear(&simpleos_fv_registry_lock, __ATOMIC_RELEASE);
}

static int simpleos_fv_register(SimpleOsFvAllocation *entries, size_t *count,
                                void *ptr, size_t bytes)
{
    if (!ptr || bytes == 0) return 0;
    uintptr_t raw = (uintptr_t)ptr;
    if (raw + bytes < raw) return 0;
    simpleos_fv_lock();
    if (*count >= SIMPLEOS_FV_REGISTRY_CAP) {
        simpleos_fv_unlock();
        return 0;
    }
    entries[*count].ptr = raw;
    entries[*count].bytes = bytes;
    *count += 1;
    simpleos_fv_unlock();
    return 1;
}

static int simpleos_fv_contains(const SimpleOsFvAllocation *entries,
                                const size_t *count, uintptr_t ptr, size_t bytes)
{
    if (!ptr || !bytes || ptr + bytes < ptr) return 0;
    simpleos_fv_lock();
    for (size_t i = 0; i < *count; ++i) {
        uintptr_t base = entries[i].ptr;
        size_t extent = entries[i].bytes;
        if (ptr >= base && ptr - base <= extent && bytes <= extent - (ptr - base)) {
            simpleos_fv_unlock();
            return 1;
        }
    }
    simpleos_fv_unlock();
    return 0;
}

int simpleos_fv_register_enum(void *ptr, size_t bytes)
{
    return simpleos_fv_register(simpleos_fv_enums, &simpleos_fv_enum_count,
                                ptr, bytes);
}

static SimpleOsFreestandingWideValueV1 *simpleos_fv_as_uint(RuntimeValue value)
{
    if (!IS_HEAP(value)) return (SimpleOsFreestandingWideValueV1 *)0;
    uintptr_t raw = (uintptr_t)DECODE_PTR(value);
    if (!raw) return 0;
    /* Identified by the box's own magic/abi/kind header, NOT by membership in
     * simpleos_fv_wide -- see the note on rt_value_u64 below. */
    SimpleOsFreestandingWideValueV1 *box = (SimpleOsFreestandingWideValueV1 *)raw;
    if (box->magic != SIMPLEOS_FV_UINT_MAGIC ||
        box->abi_version != SIMPLEOS_FV_ABI_VERSION ||
        box->kind != SIMPLEOS_FV_KIND_UINT) return 0;
    return box;
}

RuntimeValue rt_value_u64(RuntimeValue bits)
{
    SimpleOsFreestandingWideValueV1 *box =
        (SimpleOsFreestandingWideValueV1 *)SIMPLEOS_FV_ALLOC(sizeof(*box));
    /* Do NOT register into simpleos_fv_wide. That table is a fixed 4096-entry,
     * never-freed array, and rt_value_u64 boxes EVERY u64 the kernel creates --
     * LBAs, byte counts, file handles -- so any real workload exhausts it. The
     * VFS write path did exactly that and died on
     * "[PANIC] freestanding value registry: wide-value registry exhausted".
     * A monotonic fixed table cannot serve as an identity oracle for an
     * unbounded value population; the box's magic + abi_version + kind header
     * is the identity, and simpleos_fv_as_uint checks all three. This also
     * drops an O(n) spinlocked linear scan from every u64 unbox. */
    if (!box) SIMPLEOS_FV_PANIC("wide-value allocation failed");
    box->magic = SIMPLEOS_FV_UINT_MAGIC;
    box->abi_version = SIMPLEOS_FV_ABI_VERSION;
    box->kind = SIMPLEOS_FV_KIND_UINT;
    box->payload = (uint64_t)bits;
    return ENCODE_PTR(box);
}

RuntimeValue rt_value_as_u64(RuntimeValue value)
{
    SimpleOsFreestandingWideValueV1 *box = simpleos_fv_as_uint(value);
    if (box) return (RuntimeValue)box->payload;
    return value >> 3;
}

RuntimeValue rt_value_unbox_int(RuntimeValue value)
{
    SimpleOsFreestandingWideValueV1 *box = simpleos_fv_as_uint(value);
    if (box) return (RuntimeValue)box->payload;
    if (IS_INT(value)) return DECODE_INT(value);
    if (value == 11) return 1;
    if (value == 19) return 0;
    return value;
}

void *rt_struct_alloc(int64_t size)
{
    if (size <= 0) return 0;
    void *ptr = SIMPLEOS_FV_ALLOC((size_t)size);
    if (!ptr) return 0;
    /* Registration is best-effort BOOKKEEPING for rt_struct_receiver_valid, so
     * a full table must not fail the ALLOCATION. It used to: once
     * simpleos_fv_structs hit its fixed 4096 entries, rt_struct_alloc returned
     * NULL for every subsequent object even though the heap was fine. Same
     * fixed-monotonic-table defect class as the two above. */
    (void)simpleos_fv_register(simpleos_fv_structs, &simpleos_fv_struct_count,
                               ptr, (size_t)size);
    return ptr;
}

int8_t rt_struct_receiver_valid(RuntimeValue receiver,
                                RuntimeValue byte_offset,
                                RuntimeValue access_width)
{
    if (!receiver || byte_offset < 0 || access_width <= 0) return 0;
    uintptr_t base = ((uintptr_t)receiver) & ~(uintptr_t)TAG_MASK;
    uintptr_t offset = (uintptr_t)byte_offset;
    if (base + offset < base) return 0;
    return simpleos_fv_contains(simpleos_fv_structs, &simpleos_fv_struct_count,
                                base + offset, (size_t)access_width) ? 1 : 0;
}

RuntimeValue rt_unwrap_or_trap(RuntimeValue value)
{
    if (!IS_HEAP(value)) return value;
    uintptr_t raw = (uintptr_t)DECODE_PTR(value);
    if (!raw) return value;
    /* Identify the enum by its heap header, NOT by membership in
     * simpleos_fv_enums. Gating on the registry made `.unwrap()` a silent
     * NO-OP for the entire x86_64 freestanding kernel: nothing ever calls
     * simpleos_fv_register_enum (rt_enum_new in arch/x86_64/boot/
     * baremetal_stubs.c mallocs a RuntimeEnum and never registers it), so
     * simpleos_fv_enum_count is permanently 0, simpleos_fv_contains always
     * returned 0, and every `.unwrap()` fell through returning the WRAPPER
     * instead of the payload. Downstream that hands a Some-box where a class
     * receiver is expected, and the first field load off it faults -- which is
     * exactly the L5 VFS blocker (g_root_fat32.unwrap() -> Fat32Core.open+0x20,
     * `movzbq 0x48(%rax)`). See doc/08_tracking/bug/
     * vfs_l5_fat32core_open_faults_on_new_file_write_2026-08-31.md.
     *
     * The header check is the same identification the sibling accessors
     * rt_enum_id / rt_enum_discriminant / rt_enum_payload already use on this
     * exact class of value, so this makes `.unwrap()` consistent with them
     * rather than uniquely broken. It is safe: `value` is heap-tagged, so raw
     * is a real allocation, and only hdr.type (offset 0) is read before the
     * HEAP_ENUM tag proves the object really is a 24-byte RuntimeEnum. */
    SimpleOsFreestandingEnumV1 *e = (SimpleOsFreestandingEnumV1 *)raw;
    if (e->hdr.type != HEAP_ENUM) return value;
    const uint32_t ok = 2405352012u, err = 4200179024u;
    const uint32_t some = 4053299545u, none = 2371748697u;
    if (e->enum_id == 1u) {
        if (e->discriminant == some) return e->payload;
        if (e->discriminant == none) SIMPLEOS_FV_PANIC("called unwrap on None");
        return value;
    }
    if (e->discriminant == ok) return e->payload;
    if (e->discriminant == err) SIMPLEOS_FV_PANIC("called unwrap on Err");
    return value;
}
