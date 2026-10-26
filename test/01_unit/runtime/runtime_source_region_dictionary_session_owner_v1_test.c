/* SOURCE dictionary remains module-owned under a session allocator override.
 * Actual runtime owners; link runtime_native.c with SIMPLE_RUNTIME_MEMORY_OWNER.
 * This fixture does not claim SOURCE language or full compiler admission. */
#include <assert.h>
#include <stdio.h>
#include "../../../src/runtime/runtime_memory.c"
extern uint32_t rt_session_heap_begin(void);
extern int8_t rt_session_heap_end(uint32_t);
extern int8_t rt_session_alloc_begin(void);
extern int8_t rt_session_alloc_end(void);
extern int8_t rt_transient_array_scope_begin(void);
extern int8_t rt_transient_array_scope_end(void);
extern int64_t rt_dict_new(int64_t);
extern int64_t rt_source_region_dict_new_v1(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);

typedef struct SessionFixtureDictHeader {
    uint8_t kind, flags; uint16_t reserved; uint32_t scope;
    int64_t capacity, length, tombstones; void* entries;
    int64_t reader, epoch, backing;
} SessionFixtureDictHeader;
static const uint64_t rows[] = {0,8,1,0,8,8,2,1};
static const uint64_t descriptor[] = {1,4,64,2,(uintptr_t)rows,1};
static int64_t allowance(int operation, int64_t operand) {
    int64_t work = rt_source_region_bound_v1(operation,operand,0,0);
    assert(work > 0); return work;
}
int main(void) {
    uint32_t session = rt_session_heap_begin(); assert(session != 0);
    assert(rt_transient_array_scope_begin());
    int64_t ordinary = rt_dict_new(0); assert(ordinary > 0);
    uint32_t module = ((SessionFixtureDictHeader*)(uintptr_t)(ordinary & ~INT64_C(7)))->scope;
    assert(module != 0 && module != session);
    int64_t control = rt_source_region_create_v1(allowance(1,0)); assert(control > 0);
    int64_t generation = rt_source_region_created_generation_v1(control); assert(generation > 0);
    int64_t epoch = rt_source_region_stamp_v1(control,generation,allowance(4,0)); assert(epoch > 0);
    assert(rt_session_alloc_begin());
    int64_t dictionary = rt_source_region_dict_new_v1(control,generation,epoch,
        (int64_t)(uintptr_t)descriptor,0,allowance(13,(int64_t)(uintptr_t)descriptor));
    assert(dictionary > 0);
    SessionFixtureDictHeader* header = (SessionFixtureDictHeader*)(uintptr_t)(dictionary & ~INT64_C(7));
    assert(header->scope == module && header->scope != session);
    assert(sr_control(control)->members > 0);
    assert(rt_session_alloc_end());
    assert(rt_source_region_revoke_live_v1(control,generation,16) == 0);
    assert(rt_transient_array_scope_end());
    assert(sr_control(control)->members == 0);
    assert(rt_session_heap_end(session));
    assert(rt_source_region_release_live_v1(control,generation,64) == 0);
    puts("SOURCE dictionary module ownership under session override: PASS");
    return 0;
}
