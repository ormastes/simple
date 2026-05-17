#include "runtime_value.h"
#include <stdint.h>

int64_t rt_constant_time_compare(RuntimeValue a, RuntimeValue b) {
    if (rv_tag(a) != TAG_HEAP || rv_tag(b) != TAG_HEAP) return 0;

    HeapHeader *ha = (HeapHeader *)rv_as_heap_ptr(a);
    HeapHeader *hb = (HeapHeader *)rv_as_heap_ptr(b);
    if (!ha || !hb) return 0;
    if ((uintptr_t)ha < MIN_HEAP_ADDR || (uintptr_t)hb < MIN_HEAP_ADDR) return 0;
    if (ha->object_type != HEAP_TYPE_STRING || hb->object_type != HEAP_TYPE_STRING) return 0;

    RuntimeString *sa = (RuntimeString *)ha;
    RuntimeString *sb = (RuntimeString *)hb;
    if (sa->len != sb->len) return 0;
    if (sa->len == 0) return 1;

    const uint8_t *da = (const uint8_t *)(sa + 1);
    const uint8_t *db = (const uint8_t *)(sb + 1);

    uint8_t acc = 0;
    for (uint64_t i = 0; i < sa->len; i++) {
        acc |= da[i] ^ db[i];
    }
    return acc == 0 ? 1 : 0;
}
