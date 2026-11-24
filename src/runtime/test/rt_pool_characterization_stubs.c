/* Minimal providers so runtime_pool.c / runtime_thread.c link standalone for
 * rt_pool_characterization_selfcheck.c (no closures are registered: every
 * function word is a direct record, so rt_closure_func_ptr answers 0). */
#include <stdint.h>
#include <stdlib.h>

int64_t rt_closure_func_ptr(int64_t closure_value) { (void)closure_value; return 0; }
int64_t rt_closure_retain(int64_t closure_value) { (void)closure_value; return 0; }
int64_t rt_closure_release(int64_t closure_value) { (void)closure_value; return 0; }
int64_t rt_value_int(int64_t value) { return (int64_t)((uint64_t)value << 3); }
int64_t rt_value_unbox_int(int64_t value) { return value >> 3; }

#ifndef RT_POOL_CHAR_LANE_A
int g_memtrack_enabled = 0;
void spl_memtrack_record(void* ptr, int64_t size, const char* tag) { (void)ptr; (void)size; (void)tag; }
void spl_memtrack_unrecord(void* ptr) { (void)ptr; }
void simple_note_user_threads_started(void) {}
void worker_loop_entry(int64_t pool_id) { (void)pool_id; abort(); }
#endif
