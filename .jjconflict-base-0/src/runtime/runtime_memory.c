/*
 * Simple Runtime — Memory FFI Functions
 *
 * C equivalents of src/compiler_rust/runtime/src/value/ffi/memory.rs.
 * Build: cc -c -fPIC -O2 -std=gnu11 runtime_memory.c -o runtime_memory.o
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

uint8_t* rt_alloc(uint64_t size) {
    if (size == 0) return NULL;
    return (uint8_t*)calloc(1, size);
}

void rt_free(uint8_t* ptr, uint64_t size) {
    (void)size;
    free(ptr);
}

int64_t rt_ptr_read_i64(int64_t addr, int64_t offset) {
    return *(int64_t*)((char*)(uintptr_t)addr + offset);
}

int32_t rt_ptr_read_i32(int64_t addr, int64_t offset) {
    return *(int32_t*)((char*)(uintptr_t)addr + offset);
}

void rt_ptr_write_u8(int64_t addr, int64_t offset, int64_t value) {
    *(uint8_t*)((char*)(uintptr_t)addr + offset) = (uint8_t)value;
}

void rt_ptr_write_i32(int64_t addr, int64_t offset, int32_t value) {
    *(int32_t*)((char*)(uintptr_t)addr + offset) = value;
}

void rt_ptr_write_i64(int64_t addr, int64_t offset, int64_t value) {
    *(int64_t*)((char*)(uintptr_t)addr + offset) = value;
}

int64_t spl_f64_to_bits(double value) {
    int64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

int32_t spl_i64_is_zero(int64_t value) {
    return value == 0 ? 1 : 0;
}

uint8_t* rt_memset(uint8_t* dst, int8_t val, int64_t n) {
    memset(dst, (unsigned char)val, (size_t)n);
    return dst;
}

uint8_t* rt_memcpy(uint8_t* dst, const uint8_t* src, int64_t n) {
    memcpy(dst, src, (size_t)n);
    return dst;
}

uint8_t* copy_mem(uint8_t* dst, const uint8_t* src, int64_t n) {
    return rt_memcpy(dst, src, n);
}
