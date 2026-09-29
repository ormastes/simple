/* Core-C lane: behavioural proof for the four symbols that were trap-stubbed
 * in the Windows stage-2 simple_cli / simple_test_runner links (bootstrap32,
 * 2026-09-25) and sit on live `simple test` paths:
 *   rt_open_fd / rt_close_fd  -- SMF loader (compiler/99.loader/smf_mmap_native.spl)
 *   rt_get_host_target_code   -- backend_selector.spl target_code()
 *   rt_current_task_id        -- mcdc/probe_registry.spl owner id
 * Contracts mirror the Rust runtime / interpreter twins named in the block
 * comment above their definitions in runtime_native.c.
 *
 * The descriptor is also handed to rt_mmap_raw, proving rt_open_fd returns
 * the CRT descriptor spl_windows_mmap_raw expects (not an opaque token).
 *
 * Build (Windows, clang-cl):
 *   clang-cl /nologo /c /std:c11 -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -DSIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE=1 \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c /Forn.obj
 *   clang-cl /nologo src/runtime/test/rt_bootstrap_c_lane_live_stubs_selfcheck.c \
 *      rn.obj /link /FORCE:UNRESOLVED && ./rt_bootstrap_c_lane_live_stubs_selfcheck.exe
 * /FORCE:UNRESOLVED is for THIS test binary only: lld-link resolves before
 * /OPT:REF, and runtime_native.obj alone references runtime.c helpers that
 * no path exercised here calls (the POSIX recipe gets the same effect from
 * -Wl,--gc-sections). Measured 2026-09-25: 11/11 checks pass.
 * POSIX: `clang -c -std=gnu11 -ffunction-sections ...` then link with
 * `-Wl,--gc-sections -lpthread -lm -ldl`.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <io.h>
#define st_write _write
#define st_read _read
#else
#include <unistd.h>
#define st_write write
#define st_read read
#endif

extern int64_t rt_open_fd(const char* path, int64_t flags, int64_t mode);
extern int64_t rt_close_fd(int64_t fd);
extern int64_t rt_get_host_target_code(void);
extern int64_t rt_current_task_id(void);
extern int64_t rt_mmap_raw(int64_t addr, int64_t length, int64_t prot, int64_t flags,
                           int64_t fd, int64_t offset);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

/* Linux open(2) numbering shared by the loader and the Rust interpreter twin. */
#define ST_O_RDONLY 0x0
#define ST_O_WRONLY 0x1
#define ST_O_CREAT 0x40
#define ST_O_TRUNC 0x200

static int failures = 0;
#define CHECK(cond, what) do { \
    if (cond) { printf("ok   %s\n", what); } \
    else { printf("FAIL %s\n", what); failures++; } } while (0)

int main(void) {
#if defined(__x86_64__) || defined(_M_X64)
    CHECK(rt_get_host_target_code() == 0, "rt_get_host_target_code: x86_64 -> 0");
#elif defined(__aarch64__) || defined(_M_ARM64)
    CHECK(rt_get_host_target_code() == 1, "rt_get_host_target_code: aarch64 -> 1");
#endif
    CHECK(rt_current_task_id() == 0, "rt_current_task_id: no task -> 0");

    const char* path = "rt_live_stubs_selfcheck.tmp";
    const char payload[] = "SMF!payload";
    int64_t wfd = rt_open_fd(path, ST_O_WRONLY | ST_O_CREAT | ST_O_TRUNC, 0644);
    CHECK(wfd >= 0, "rt_open_fd: create+truncate (raw C string path)");
    if (wfd >= 0) {
        CHECK(st_write((int)wfd, payload, (unsigned)sizeof(payload)) == (int)sizeof(payload),
              "write through the returned descriptor");
        CHECK(rt_close_fd(wfd) == 0, "rt_close_fd: close written fd");
    }

    /* Native code passes `path: text` as one boxed RuntimeValue word. */
    int64_t boxed = rt_string_new((const uint8_t*)path, (uint64_t)strlen(path));
    int64_t rfd = rt_open_fd((const char*)(uintptr_t)boxed, ST_O_RDONLY, 0);
    CHECK(rfd >= 0, "rt_open_fd: read-only (boxed text path)");
    if (rfd >= 0) {
        char buf[sizeof(payload)] = {0};
        CHECK(st_read((int)rfd, buf, (unsigned)sizeof(payload)) == (int)sizeof(payload) &&
              memcmp(buf, payload, sizeof(payload)) == 0, "read back payload");
        /* PROT_READ=1, MAP_PRIVATE=2: the loader's mapping shape. */
        int64_t map = rt_mmap_raw(0, (int64_t)sizeof(payload), 1, 2, rfd, 0);
        CHECK(map > 0 && memcmp((const void*)(uintptr_t)map, payload, sizeof(payload)) == 0,
              "rt_mmap_raw maps the rt_open_fd descriptor");
        CHECK(rt_close_fd(rfd) == 0, "rt_close_fd: close read fd");
    }
    CHECK(rt_open_fd("rt_live_stubs_selfcheck.missing", ST_O_RDONLY, 0) == -1,
          "rt_open_fd: missing file -> -1");
    CHECK(rt_close_fd(-1) == -1, "rt_close_fd: -1 -> -1");
    remove(path);

    if (failures) {
        printf("FAIL - %d check(s) failed\n", failures);
        return 1;
    }
    printf("PASS - live-stub core-C symbols behave per the Rust contracts\n");
    return 0;
}
