/*
 * SimpleOS Shared Baremetal Runtime — Header
 *
 * Architecture-independent type definitions, tagged-value macros,
 * and forward declarations for the shared baremetal runtime.
 *
 * USAGE:
 *   1. #include <stdint.h> and <stddef.h> in the arch-specific file
 *   2. Define the following arch-specific functions BEFORE including this header:
 *        static void serial_putchar(char c);
 *        static void serial_puts(const char *s);
 *        static void serial_put_hex(uint64_t v);
 *        static void serial_put_dec(int64_t v);
 *        static void arch_halt_forever(void);
 *        static void arch_pause(void);
 *   3. #include "baremetal_runtime.h"
 *   4. #include "baremetal_runtime.c"
 *
 * The arch-specific file provides _start(), serial I/O, port I/O,
 * MMIO, PCI, NVMe, framebuffer, syscall dispatch, and CPU control.
 */

#ifndef BAREMETAL_RUNTIME_H
#define BAREMETAL_RUNTIME_H

#include <stdint.h>
#include <stddef.h>

/* ===================================================================
 * RuntimeValue — tagged 64-bit value
 * =================================================================== */

typedef int64_t RuntimeValue;

/* ===================================================================
 * Tag encoding
 * =================================================================== */

#define TAG_MASK    0x7ULL
#define TAG_INT     0x0ULL
#define TAG_HEAP    0x1ULL
#define TAG_FLOAT   0x2ULL
#define TAG_SPECIAL 0x3ULL

#define ENCODE_INT(v)  ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3) | TAG_INT))
#define DECODE_INT(v)  ((int64_t)((uint64_t)(v) >> 3))

#define ENCODE_PTR(p)  ((RuntimeValue)((uint64_t)(uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v)  ((void*)((uint64_t)(v) & ~TAG_MASK))

#define IS_INT(v)      (((uint64_t)(v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v)     (((uint64_t)(v) & TAG_MASK) == TAG_HEAP)
#define IS_FLOAT(v)    (((uint64_t)(v) & TAG_MASK) == TAG_FLOAT)
#define IS_SPECIAL(v)  (((uint64_t)(v) & TAG_MASK) == TAG_SPECIAL)
#define IS_NIL(v)      ((v) == (RuntimeValue)TAG_SPECIAL)

#define NIL_VALUE      ((RuntimeValue)TAG_SPECIAL)
#define TRUE_VALUE     ENCODE_INT(1)
#define FALSE_VALUE    ENCODE_INT(0)

/* The values CODEGEN actually produces and consumes for a Simple `bool`.
 *
 * These are TAG_SPECIAL payloads, not encoded ints, so they are NOT the same as
 * TRUE_VALUE (8) / FALSE_VALUE (0) above -- see
 * doc/08_tracking/bug/baremetal_bool_macros_disagree_with_codegen_tags_2026-09-01.md,
 * which tracks that older pair's disagreement with codegen as its own defect.
 * These two are added, and the older pair deliberately left alone, so that
 * fixing the tagged-bool decode does not silently change every existing
 * TRUE_VALUE / FALSE_VALUE call site as a side effect.
 *
 * Source of truth: src/compiler_rust/compiler/src/codegen/llvm/instructions.rs
 * (`tagged_bool_const`: true = 11, false = 19). Pinned by
 * scripts/check/check-baremetal-tagged-bool-decode.shs. */
#define TAGGED_BOOL_TRUE   ((RuntimeValue)11)
#define TAGGED_BOOL_FALSE  ((RuntimeValue)19)

/* ===================================================================
 * Heap object types
 * =================================================================== */

#define HEAP_STRING 1
#define HEAP_ARRAY  2
#define HEAP_MAP    3
#define HEAP_OBJECT 4

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

/* len MUST be uint64_t (data therefore at offset 16). Codegen inlines
 * `text.len()` as an i64 load at offset 8 and emits string objects with a
 * 64-bit length, so a uint32_t here makes every .len() read the low 4 bytes
 * of data as the high half of the length, and shifts every data access 4
 * bytes early. Fixed 2026-07-12 (x86_64), silently reverted by the tree wipe
 * 6f86ff32a7d, re-applied 2026-08-31 after the same defect stalled the
 * riscv64 in-guest components lane.
 * See doc/08_tracking/bug/x64_rt_extras_runtime_string_layout_mismatch.md */
typedef struct {
    HeapHeader hdr;
    uint64_t   len;
    char       data[];
} RuntimeString;
_Static_assert(offsetof(RuntimeString, len) == 8, "RuntimeString.len must sit at offset 8: codegen inlines .len() as an i64 load there");
_Static_assert(offsetof(RuntimeString, data) == 16, "RuntimeString.data must sit at offset 16 to match compiler-emitted string objects");

typedef struct {
    HeapHeader   hdr;
    uint32_t     len;
    uint32_t     cap;
    RuntimeValue items[];
} RuntimeArray;

typedef struct {
    HeapHeader    hdr;
    uint32_t      len;
    uint32_t      cap;
    RuntimeValue *keys;
    RuntimeValue *values;
} RuntimeMap;

/* ===================================================================
 * Forward declarations for functions used before definition
 * =================================================================== */

RuntimeValue rt_map_clone(RuntimeValue map);
RuntimeValue rt_map_new(void);
RuntimeValue rt_map_set(RuntimeValue map, RuntimeValue key, RuntimeValue value);
RuntimeValue rt_map_get(RuntimeValue map, RuntimeValue key);
RuntimeValue rt_array_new(RuntimeValue cap_val);
int8_t rt_array_push(RuntimeValue arr, RuntimeValue val);
RuntimeValue rt_string_concat(RuntimeValue a, RuntimeValue b);
RuntimeValue rt_string_from_cstr(const char *cstr);
RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len_val);
RuntimeValue rt_native_eq(RuntimeValue a, RuntimeValue b);
RuntimeValue rt_value_to_string(RuntimeValue val);
RuntimeValue rt_value_format_string(RuntimeValue val, RuntimeValue fmt_ptr, RuntimeValue fmt_len);
RuntimeValue rt_string_format(RuntimeValue fmt, RuntimeValue val);
void rt_print_value(RuntimeValue val);

/* ===================================================================
 * Arch-specific function contracts (must be defined before
 * #include "baremetal_runtime.c"):
 *
 *   static void serial_putchar(char c);
 *   static void serial_puts(const char *s);
 *   static void serial_put_hex(uint64_t v);
 *   static void serial_put_dec(int64_t v);
 *   static void arch_halt_forever(void);
 *   static void arch_pause(void);
 * =================================================================== */

#endif /* BAREMETAL_RUNTIME_H */
