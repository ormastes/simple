#include <stdlib.h>

/* runtime_native.c is a single large translation unit. These symbols belong to
 * unrelated runtime capsules and are never reached by this focused executable.
 * Abort if link-closure drift makes any of them live in the tested call path. */
#define UNREACHED_STUB(name) void name(void) { abort(); }

UNREACHED_STUB(spl_strdup)
UNREACHED_STUB(spl_print)
UNREACHED_STUB(spl_println)
UNREACHED_STUB(spl_str_new)
UNREACHED_STUB(spl_panic)
UNREACHED_STUB(rt_simd_has_avx2)
UNREACHED_STUB(rt_simd_has_sse)
UNREACHED_STUB(rt_simd_has_neon)
UNREACHED_STUB(rt_simd_has_rvv)
UNREACHED_STUB(rt_text_slice_audit_level)
UNREACHED_STUB(rt_text_slice_audit_note)
UNREACHED_STUB(spl_str_len)
UNREACHED_STUB(spl_str_concat)
UNREACHED_STUB(spl_str_slice)
UNREACHED_STUB(spl_str_index_of)
UNREACHED_STUB(spl_str_replace)
UNREACHED_STUB(spl_str_cmp)
UNREACHED_STUB(rt_getcwd)
UNREACHED_STUB(rt_sleep_ms_native)
UNREACHED_STUB(rt_process_spawn_async)
UNREACHED_STUB(rt_process_wait)
UNREACHED_STUB(rt_process_spawn_guarded)
UNREACHED_STUB(rt_process_run_timeout)
UNREACHED_STUB(rt_process_run_bounded)
UNREACHED_STUB(spl_file_read)
UNREACHED_STUB(rt_dir_remove_all)
UNREACHED_STUB(rt_is_dir)
UNREACHED_STUB(spl_env_get)
