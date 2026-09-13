/* Stage2 bootstrap link (core-C-only lane): behavioural proof for 30 of the
 * "bucket 2, Rust-only misc" symbols added to runtime_native.c to close part
 * of the undefined-symbol set found when relinking the real Stage2 failed-
 * link object set (native-objects-8HIZif, run22, 2026-09-07) with
 * `-Wl,--error-limit=0` instead of the linker's default 20-error cutoff --
 * see doc/08_tracking/bug/stage2_link_full_undefined_symbol_census_2026-09-07.md.
 *
 * Covers: rt_time_now_seconds, rt_remove, rt_file_fsync; the rt_progress_*
 * thread-local clock family; rt_load_barrier/rt_store_barrier;
 * rt_path_basename/rt_path_ext/rt_path_separator; rt_random_randint/
 * rt_random_uniform; rt_typed_bytes_u8_data_at; rt_mem_attr_enabled/
 * rt_mem_attr_set_owner; the rt_log_* family; rt_munmap/rt_msync/rt_madvise;
 * rt_file_lock/rt_file_unlock.
 *
 * Build (links against the standalone-compiled runtime_native.o, i.e. the
 * exact TU the core-C bootstrap archive is made from -- same recipe as
 * rt_runtime_kind_probes_core_c_selfcheck.c beside this file):
 *   cc -c -std=gnu11 -ffunction-sections -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -mno-outline-atomics \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o rn.o
 *   cc -std=gnu11 -Wl,--gc-sections \
 *      src/runtime/test/rt_bootstrap_c_lane_bucket2_misc_selfcheck.c \
 *      rn.o -lpthread -lm -ldl -o selfcheck && ./selfcheck
 */
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/mman.h>
#include <stdlib.h>

extern int64_t rt_time_now_seconds(void);
/* rt_remove takes a single boxed RuntimeValue text handle (see the code
 * comment beside its definition for the disassembly evidence), not a raw
 * C-string pointer -- box the path with rt_string_new before calling it. */
extern int64_t rt_remove(int64_t path_value);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int rt_file_fsync(const uint8_t* path_ptr, uint64_t path_len);

extern int64_t rt_progress_clock_now_nanos(void);
extern bool rt_progress_tls_is_initialized(void);
extern int64_t rt_progress_tls_start_nanos(void);
extern void rt_progress_tls_store_start_nanos(int64_t start_nanos);
extern void rt_progress_tls_clear(void);

extern void rt_load_barrier(void);
extern void rt_store_barrier(void);

extern int64_t rt_path_basename(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_path_ext(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_path_separator(void);
extern int64_t rt_string_len(int64_t string);
extern const uint8_t* rt_string_data(int64_t string);

extern int64_t rt_random_randint(int64_t min, int64_t max);
extern double rt_random_uniform(double min, double max);

extern int64_t rt_typed_bytes_u8_data_at(int64_t data_ptr, int64_t index);

extern int64_t rt_mem_attr_enabled(void);
extern void rt_mem_attr_set_owner(const uint8_t* name_ptr, uint64_t name_len);

extern void rt_log_set_global_level(int64_t level);
extern int64_t rt_log_get_global_level(void);
extern void rt_log_set_scope_level(const uint8_t* scope_ptr, uint64_t scope_len, int64_t level);
extern int64_t rt_log_get_scope_level(const uint8_t* scope_ptr, uint64_t scope_len);
extern void rt_log_clear_scope_levels(void);
extern void rt_log_emit(int64_t level, const uint8_t* scope_ptr, uint64_t scope_len,
                          const uint8_t* msg_ptr, uint64_t msg_len);
extern int64_t rt_log_is_enabled(int64_t level, const uint8_t* scope_ptr, uint64_t scope_len);

extern bool rt_munmap(int64_t addr, int64_t size);
extern bool rt_msync(int64_t addr, int64_t size);
extern bool rt_madvise(int64_t addr, int64_t size, int64_t advice);

extern int64_t rt_file_lock(const uint8_t* path_ptr, uint64_t path_len, int64_t timeout_secs);
extern bool rt_file_unlock(int64_t handle);

static int failures = 0;

#define CHECK(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL: %s\n", msg); failures++; } \
} while (0)

static void check_time_remove_fsync(void) {
    int64_t now = rt_time_now_seconds();
    time_t libc_now = time(NULL);
    CHECK(now > 0, "rt_time_now_seconds must be positive (post-epoch)");
    CHECK(llabs((long long)now - (long long)libc_now) <= 2,
          "rt_time_now_seconds must agree with libc time(NULL) within 2s");

    char path[] = "/tmp/rt_bucket2_selfcheck_XXXXXX";
    int fd = mkstemp(path);
    CHECK(fd >= 0, "mkstemp for rt_remove/rt_file_fsync fixture must succeed");
    if (fd >= 0) {
        const char* data = "hello";
        CHECK(write(fd, data, 5) == 5, "fixture write must succeed");
        close(fd);
        CHECK(rt_file_fsync((const uint8_t*)path, (uint64_t)strlen(path)) == 1,
              "rt_file_fsync on an existing regular file returns 1");
        int64_t boxed_path = rt_string_new((const uint8_t*)path, (uint64_t)strlen(path));
        CHECK(rt_remove(boxed_path) == 0, "rt_remove on an existing file returns 0");
        CHECK(access(path, F_OK) != 0, "rt_remove must actually unlink the file");
        int64_t boxed_path2 = rt_string_new((const uint8_t*)path, (uint64_t)strlen(path));
        CHECK(rt_remove(boxed_path2) < 0, "rt_remove on a now-missing file returns a negative errno");
    }
}

static void check_progress(void) {
    rt_progress_tls_clear();
    CHECK(!rt_progress_tls_is_initialized(), "rt_progress_tls_clear resets initialized to false");
    CHECK(rt_progress_tls_start_nanos() == 0, "rt_progress_tls_clear resets start_nanos to 0");

    int64_t a = rt_progress_clock_now_nanos();
    CHECK(a >= 0, "rt_progress_clock_now_nanos first reading must be non-negative");
    rt_progress_tls_store_start_nanos(a);
    CHECK(rt_progress_tls_is_initialized(), "rt_progress_tls_store_start_nanos sets initialized true");
    CHECK(rt_progress_tls_start_nanos() == a, "rt_progress_tls_start_nanos reads back stored value");

    struct timespec ts = {0, 20 * 1000 * 1000}; /* 20ms */
    nanosleep(&ts, NULL);
    int64_t b = rt_progress_clock_now_nanos();
    CHECK(b > a, "rt_progress_clock_now_nanos must strictly increase across a real sleep");

    rt_progress_tls_clear();
    CHECK(!rt_progress_tls_is_initialized(), "rt_progress_tls_clear resets state again");
}

static void check_barriers(void) {
    /* No observable state from a single thread; this proves linkage and
     * that the fence intrinsics do not trap. */
    rt_load_barrier();
    rt_store_barrier();
    CHECK(1, "rt_load_barrier/rt_store_barrier callable without trapping");
}

static int text_equals(int64_t rv, const char* expected) {
    int64_t len = rt_string_len(rv);
    const uint8_t* data = rt_string_data(rv);
    size_t elen = strlen(expected);
    if ((uint64_t)len != (uint64_t)elen) return 0;
    if (elen == 0) return 1;
    return memcmp(data, expected, elen) == 0;
}

static void check_path(void) {
    int64_t sep = rt_path_separator();
    CHECK(text_equals(sep, "/"), "rt_path_separator returns \"/\" on this platform");

    const char* p1 = "/a/b/c.txt";
    CHECK(text_equals(rt_path_basename((const uint8_t*)p1, strlen(p1)), "c.txt"),
          "rt_path_basename(\"/a/b/c.txt\") == \"c.txt\"");
    CHECK(text_equals(rt_path_ext((const uint8_t*)p1, strlen(p1)), "txt"),
          "rt_path_ext(\"/a/b/c.txt\") == \"txt\"");

    /* Rust's Path::components() treats a trailing separator as insignificant
     * (it is not its own component), so file_name() still returns the last
     * real component here -- "" is reserved for paths with NO real component
     * left at all (empty, "/", ".", "..", or an all-separator string). */
    const char* p2 = "/a/b/";
    CHECK(text_equals(rt_path_basename((const uint8_t*)p2, strlen(p2)), "b"),
          "rt_path_basename(\"/a/b/\") == \"b\" (trailing slash is not its own component)");
    const char* p2_root = "/";
    CHECK(text_equals(rt_path_basename((const uint8_t*)p2_root, strlen(p2_root)), ""),
          "rt_path_basename(\"/\") == \"\" (root has no file_name)");
    const char* p2_dotdot = "/a/..";
    CHECK(text_equals(rt_path_basename((const uint8_t*)p2_dotdot, strlen(p2_dotdot)), ""),
          "rt_path_basename(\"/a/..\") == \"\" (a \"..\" final component has no file_name)");

    const char* p3 = ".bashrc";
    CHECK(text_equals(rt_path_basename((const uint8_t*)p3, strlen(p3)), ".bashrc"),
          "rt_path_basename(\".bashrc\") == \".bashrc\"");
    CHECK(text_equals(rt_path_ext((const uint8_t*)p3, strlen(p3)), ""),
          "rt_path_ext(\".bashrc\") == \"\" (leading dot is not an extension)");

    const char* p4 = "archive.tar.gz";
    CHECK(text_equals(rt_path_ext((const uint8_t*)p4, strlen(p4)), "gz"),
          "rt_path_ext(\"archive.tar.gz\") == \"gz\" (only the last extension)");
}

static void check_random(void) {
    CHECK(rt_random_randint(5, 5) == 5, "rt_random_randint(5,5) == 5 (single-value range)");
    CHECK(rt_random_randint(10, 3) == 10, "rt_random_randint(min>max) returns min unchanged");
    for (int i = 0; i < 200; i++) {
        int64_t v = rt_random_randint(1, 6);
        if (v < 1 || v > 6) { CHECK(0, "rt_random_randint(1,6) must stay in [1,6]"); break; }
    }
    for (int i = 0; i < 200; i++) {
        double v = rt_random_uniform(2.0, 3.0);
        if (v < 2.0 || v >= 3.0) { CHECK(0, "rt_random_uniform(2,3) must stay in [2,3)"); break; }
    }
}

static void check_typed_bytes(void) {
    uint8_t buf[4] = {10, 20, 30, 40};
    CHECK(rt_typed_bytes_u8_data_at((int64_t)(intptr_t)buf, 0) == 10, "byte[0] == 10");
    CHECK(rt_typed_bytes_u8_data_at((int64_t)(intptr_t)buf, 3) == 40, "byte[3] == 40");
}

static void check_mem_attr(void) {
    unsetenv("SIMPLE_MEM_ATTR");
    /* NOTE: the gate caches its first read for the process lifetime (matches
     * heap.rs's ATTR_GATE), so this process's answer is fixed by whichever
     * env state existed at the first call anywhere in this binary -- assert
     * only that the accessor returns a stable 0/1 and that set_owner never
     * crashes regardless of the gate's state. */
    int64_t enabled = rt_mem_attr_enabled();
    CHECK(enabled == 0 || enabled == 1, "rt_mem_attr_enabled returns 0 or 1");
    CHECK(rt_mem_attr_enabled() == enabled, "rt_mem_attr_enabled is stable across repeated calls");
    const char* owner = "selfcheck";
    rt_mem_attr_set_owner((const uint8_t*)owner, strlen(owner));
    rt_mem_attr_set_owner(NULL, 0); /* null pointer must be a safe no-op */
    CHECK(1, "rt_mem_attr_set_owner callable without crashing");
}

static void check_log(void) {
    rt_log_clear_scope_levels();
    rt_log_set_global_level(4);
    CHECK(rt_log_get_global_level() == 4, "rt_log_set/get_global_level round-trips");

    const char* scope = "selfcheck_scope";
    uint64_t scope_len = (uint64_t)strlen(scope);
    CHECK(rt_log_get_scope_level((const uint8_t*)scope, scope_len) == 4,
          "unset scope falls back to global level");
    rt_log_set_scope_level((const uint8_t*)scope, scope_len, 7);
    CHECK(rt_log_get_scope_level((const uint8_t*)scope, scope_len) == 7,
          "rt_log_set/get_scope_level round-trips");
    CHECK(rt_log_get_global_level() == 4, "setting a scope level must not change the global level");

    CHECK(rt_log_is_enabled(7, (const uint8_t*)scope, scope_len) == 1,
          "level == scope level is enabled");
    CHECK(rt_log_is_enabled(8, (const uint8_t*)scope, scope_len) == 0,
          "level above scope level is disabled");
    CHECK(rt_log_is_enabled(1, (const uint8_t*)scope, scope_len) == 1,
          "level well below scope level is enabled");

    rt_log_clear_scope_levels();
    CHECK(rt_log_get_scope_level((const uint8_t*)scope, scope_len) == 4,
          "rt_log_clear_scope_levels removes the override, falls back to global");

    /* Emission itself has no return value to assert on; call it at a level
     * that is enabled and one that is suppressed to prove both paths run
     * without crashing (output goes to stderr, inspected manually above). */
    rt_log_emit(2, (const uint8_t*)"emit_scope", 10, (const uint8_t*)"visible message", 15);
    rt_log_set_global_level(0);
    rt_log_emit(2, NULL, 0, (const uint8_t*)"suppressed message", 18);
    rt_log_set_global_level(4);
}

static void check_mmap_family(void) {
    long page = sysconf(_SC_PAGESIZE);
    void* addr = mmap(NULL, (size_t)page, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    CHECK(addr != MAP_FAILED, "fixture mmap for rt_munmap/rt_msync/rt_madvise must succeed");
    if (addr != MAP_FAILED) {
        int64_t iaddr = (int64_t)(intptr_t)addr;
        CHECK(rt_madvise(iaddr, page, 4) == true, "rt_madvise(MADV_DONTNEED=4) succeeds on a mapped region");
        CHECK(rt_madvise(iaddr, page, 99) == false, "rt_madvise rejects an unknown advice code");
        CHECK(rt_msync(iaddr, page) == true, "rt_msync succeeds on a mapped region");
        CHECK(rt_munmap(iaddr, page) == true, "rt_munmap succeeds on a mapped region");
        CHECK(rt_munmap(0, page) == false, "rt_munmap rejects a null address");
    }
}

static void check_file_lock(void) {
    char path[] = "/tmp/rt_bucket2_selfcheck_lock_XXXXXX";
    int fd = mkstemp(path);
    CHECK(fd >= 0, "mkstemp for rt_file_lock fixture must succeed");
    if (fd >= 0) {
        close(fd);
        int64_t handle = rt_file_lock((const uint8_t*)path, strlen(path), 0);
        CHECK(handle >= 0, "rt_file_lock on a real file returns a non-negative descriptor");
        CHECK(rt_file_unlock(handle) == true, "rt_file_unlock releases and closes cleanly");
        unlink(path);
    }
}

int main(void) {
    check_time_remove_fsync();
    check_progress();
    check_barriers();
    check_path();
    check_random();
    check_typed_bytes();
    check_mem_attr();
    check_log();
    check_mmap_family();
    check_file_lock();
    if (failures == 0) {
        printf("PASS: bootstrap core-C lane bucket2-misc additions behave correctly\n");
        return 0;
    }
    fprintf(stderr, "FAIL: %d assertion(s) failed\n", failures);
    return 1;
}
