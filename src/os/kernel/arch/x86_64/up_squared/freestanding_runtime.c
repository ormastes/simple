/* Freestanding allocation provider for the UP Squared ring-0 kernel.
 *
 * The x86_64 SimpleOS sysroot also contains a userspace malloc whose
 * growth path enters the kernel through `syscall`.  A kernel image cannot use
 * that ABI before (or after) entering ring 0.  Keep allocation inside the
 * linker-owned heap and make this object the malloc owner selected by the
 * Simple core archive.
 */
#include <stddef.h>
#include <stdint.h>

extern unsigned char __heap_start[];
extern unsigned char __heap_end[];

typedef struct Up2HeapHeader {
    uint64_t size;
} Up2HeapHeader;

static uintptr_t up2_heap_next;

void *memcpy(void *destination, const void *source, size_t count) {
    unsigned char *out = (unsigned char *)destination;
    const unsigned char *in = (const unsigned char *)source;
    for (size_t index = 0u; index < count; ++index) {
        out[index] = in[index];
    }
    return destination;
}

void *memset(void *destination, int value, size_t count) {
    unsigned char *out = (unsigned char *)destination;
    for (size_t index = 0u; index < count; ++index) {
        out[index] = (unsigned char)value;
    }
    return destination;
}

int memcmp(const void *left, const void *right, size_t count) {
    const unsigned char *a = (const unsigned char *)left;
    const unsigned char *b = (const unsigned char *)right;
    for (size_t index = 0u; index < count; ++index) {
        if (a[index] != b[index]) {
            return a[index] < b[index] ? -1 : 1;
        }
    }
    return 0;
}

size_t strlen(const char *text) {
    size_t length = 0u;
    while (text[length] != '\0') {
        ++length;
    }
    return length;
}

static int up2_align16(size_t value, size_t *aligned) {
    if (value > SIZE_MAX - 15u) {
        return 0;
    }
    *aligned = (value + 15u) & ~(size_t)15u;
    return 1;
}

void *malloc(size_t size) {
    size_t payload;
    if (size == 0u) {
        size = 1u;
    }
    if (!up2_align16(size, &payload)) {
        return (void *)0;
    }

    uintptr_t start = (uintptr_t)__heap_start;
    uintptr_t limit = (uintptr_t)__heap_end;
    uintptr_t next = up2_heap_next == 0u ? start : up2_heap_next;
    if (next < start || next > limit ||
        payload > (size_t)(limit - next) ||
        sizeof(Up2HeapHeader) > (size_t)(limit - next) - payload) {
        return (void *)0;
    }

    Up2HeapHeader *header = (Up2HeapHeader *)next;
    header->size = (uint64_t)payload;
    up2_heap_next = next + sizeof(*header) + payload;
    return (void *)(header + 1);
}

void free(void *pointer) {
    (void)pointer;
}

void *calloc(size_t count, size_t size) {
    if (size != 0u && count > SIZE_MAX / size) {
        return (void *)0;
    }
    size_t total = count * size;
    unsigned char *result = (unsigned char *)malloc(total);
    if (result == (void *)0) {
        return (void *)0;
    }
    for (size_t index = 0u; index < total; ++index) {
        result[index] = 0u;
    }
    return result;
}

void *realloc(void *pointer, size_t size) {
    if (pointer == (void *)0) {
        return malloc(size);
    }
    if (size == 0u) {
        return (void *)0;
    }

    Up2HeapHeader *old_header = ((Up2HeapHeader *)pointer) - 1;
    size_t old_size = (size_t)old_header->size;
    unsigned char *result = (unsigned char *)malloc(size);
    if (result == (void *)0) {
        return (void *)0;
    }
    size_t copy_size = old_size < size ? old_size : size;
    const unsigned char *old = (const unsigned char *)pointer;
    for (size_t index = 0u; index < copy_size; ++index) {
        result[index] = old[index];
    }
    return result;
}

/* Minimal ring-0 providers required by the shared NVMe/storage closure. */
int64_t syscall(uint64_t id, uint64_t arg0, uint64_t arg1, uint64_t arg2,
                uint64_t arg3, uint64_t arg4) {
    (void)id; (void)arg0; (void)arg1; (void)arg2; (void)arg3; (void)arg4;
    return -38;
}

uint64_t unsafe_addr_of(int64_t value) { return (uint64_t)value; }

int64_t rt_volatile_read_u8(int64_t address) {
    return *(volatile uint8_t *)(uintptr_t)address;
}
int64_t rt_volatile_read_u32(int64_t address) {
    return *(volatile uint32_t *)(uintptr_t)address;
}
int64_t rt_volatile_read_u64(int64_t address) {
    return (int64_t)*(volatile uint64_t *)(uintptr_t)address;
}
void rt_volatile_write_u8(int64_t address, int64_t value) {
    *(volatile uint8_t *)(uintptr_t)address = (uint8_t)value;
}
void rt_volatile_write_u32(int64_t address, int64_t value) {
    *(volatile uint32_t *)(uintptr_t)address = (uint32_t)value;
}
void rt_volatile_write_u64(int64_t address, int64_t value) {
    *(volatile uint64_t *)(uintptr_t)address = (uint64_t)value;
}

int64_t rt_text_slice_audit_note_range(int64_t source, int64_t source_length,
                                       int64_t begin, int64_t finish) {
    (void)source; (void)source_length; (void)begin; (void)finish;
    return 0;
}

extern int64_t rt_array_len_safe(int64_t value);
extern int64_t rt_array_data_ptr(int64_t value);
extern int64_t rt_string_new(int64_t bytes, int64_t length);

int64_t rt_bytes_to_text(int64_t value) {
    int64_t length = rt_array_len_safe(value);
    if (value == 0 || length <= 0) {
        return rt_string_new(0, 0);
    }
    return rt_string_new(rt_array_data_ptr(value), length);
}

long long strtoll(const char *text, char **end, int base) {
    const char *cursor = text;
    long long sign = 1;
    unsigned long long value = 0;
    if (base != 0 && base != 10) {
        if (end != (char **)0) *end = (char *)text;
        return 0;
    }
    while (*cursor == ' ' || *cursor == '\t' || *cursor == '\r' || *cursor == '\n') cursor++;
    if (*cursor == '-' || *cursor == '+') {
        if (*cursor == '-') sign = -1;
        cursor++;
    }
    while (*cursor >= '0' && *cursor <= '9') {
        value = value * 10u + (unsigned long long)(*cursor - '0');
        cursor++;
    }
    if (end != (char **)0) *end = (char *)cursor;
    return sign < 0 ? -(long long)value : (long long)value;
}
