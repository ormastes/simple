/* Link stubs for rt_clear_receiver_dispatch_harness.c.
 *
 * runtime_native.c references a handful of symbols that live in the OTHER
 * runtime translation units (spl_* string/IO helpers, process spawn, SIMD
 * capability probes). None of them is on the rt_clear receiver-dispatch path
 * under test. Stubbing them keeps the harness a single-TU, seconds-long build
 * instead of requiring the whole runtime link.
 *
 * Policy: anything that is genuinely unreachable from the harness aborts, so a
 * silent wrong answer is impossible. The two audit hooks return a benign 0
 * because rt_string_new consults them on the path rt_clear takes for its
 * string-receiver return value.
 */
#include <stdlib.h>
#include <stdio.h>

static void unreachable(const char* name) {
    fprintf(stderr, "harness stub: %s is not on the rt_clear path but was called\n", name);
    abort();
}

#define STUB(name) long name(void) { unreachable(#name); return 0; }

STUB(rt_dir_remove_all)
STUB(rt_getcwd)
STUB(rt_is_dir)
STUB(rt_process_run_bounded)
STUB(rt_process_run_timeout)
STUB(rt_process_spawn_async)
STUB(rt_process_spawn_guarded)
STUB(rt_process_wait)
STUB(rt_sleep_ms_native)
STUB(spl_env_get)
STUB(spl_file_read)
STUB(spl_panic)
STUB(spl_print)
STUB(spl_println)
STUB(spl_str_cmp)
STUB(spl_str_concat)
STUB(spl_strdup)
STUB(spl_str_index_of)
STUB(spl_str_len)
STUB(spl_str_new)
STUB(spl_str_replace)
STUB(spl_str_slice)

/* SIMD capability probes: report "no acceleration". Benign and deterministic. */
int rt_simd_has_avx2(void) { return 0; }
int rt_simd_has_sse(void) { return 0; }
int rt_simd_has_neon(void) { return 0; }
int rt_simd_has_rvv(void) { return 0; }

/* Text-slice audit hooks: level 0 = auditing off. */
int rt_text_slice_audit_level(void) { return 0; }
void rt_text_slice_audit_note(const char* a, long b, long c) { (void)a; (void)b; (void)c; }
