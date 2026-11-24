/* Characterization selfcheck for the file-io twins shared by runtime.c and
 * runtime_native.c through the private static headers
 *   runtime_file_exists_probe_impl.h  (rt_file_exists_probe_begin/end)
 *   runtime_file_stat_impl.h          (rt_file_is_regular_no_follow, rt_file_is_char_device)
 *   runtime_file_fsync_impl.h         (rt_file_fsync worker)
 *   runtime_file_slurp_impl.h         (rt_file_read_text grow-and-read loop)
 * Linked once against each provider by
 * scripts/check/check-runtime-file-io-impl-selfcheck.shs. Pins the observable
 * contracts before and after the dedup; it never reaches into provider state. */
#include <stdio.h>

#if defined(_WIN32)
/* POSIX-only witness (symlink/mkdir/fsync + /dev/null): exit 77 (SKIP). */
int main(void) { puts("SKIP: POSIX-only file-io twins witness"); return 77; }
#elif defined(SIMPLE_TEST_CORE_RUNTIME)
/* c-runtime test kind: this harness is linked against a whole provider TU by
 * scripts/check/check-runtime-file-io-impl-selfcheck.shs. Exit 64 = needs its
 * owning harness; never counted as a pass. */
int main(void) {
    fputs("rt_file_io_twins_selfcheck: needs its owning harness (see file header)\n", stderr);
    return 64;
}
#else
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/stat.h>

extern bool rt_file_is_regular_no_follow(const uint8_t* path_ptr, uint64_t path_len);
extern int rt_file_is_char_device(const uint8_t* path_ptr, uint64_t path_len);
extern int rt_file_fsync(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_file_read_text(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_file_exists_probe_begin(void);
extern int64_t rt_file_exists_probe_end(int64_t token);
extern bool rt_file_exists(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_string_len(int64_t value);
extern const uint8_t* rt_string_data(int64_t value);

#if defined(RT_FILE_IO_TWINS_STUB_STRINGS)
/* runtime.c does not define the text constructor it calls (its owner lives in
 * another TU of the seed image). Supply a minimal boxed text so the runtime.c
 * lane links standalone; the native lane uses its own rt_string_*. */
typedef struct { int64_t len; uint8_t* data; } StubText;
int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    StubText* s = (StubText*)malloc(sizeof(StubText));
    if (!s) return 3;
    s->len = (int64_t)len;
    s->data = (uint8_t*)malloc(len ? len : 1);
    if (!s->data) { free(s); return 3; }
    if (len) memcpy(s->data, bytes, len);
    return (int64_t)(intptr_t)s;
}
int64_t rt_string_len(int64_t value) { return ((StubText*)(intptr_t)value)->len; }
const uint8_t* rt_string_data(int64_t value) { return ((StubText*)(intptr_t)value)->data; }
#endif

#define T(s) (const uint8_t*)(s), (uint64_t)strlen(s)
#define CHECK(c) do { if (!(c)) { printf("FAIL line %d: %s\n", __LINE__, #c); return 1; } } while (0)

int main(void) {
    char dir[512], file[600], link_path[600], missing[600];
    const char* tmp = getenv("TMPDIR");
    if (!tmp) tmp = "/tmp";
    snprintf(dir, sizeof(dir), "%s/rt_file_io_twins.%d", tmp, (int)getpid());
    snprintf(file, sizeof(file), "%s/regular.bin", dir);
    snprintf(link_path, sizeof(link_path), "%s/regular.lnk", dir);
    snprintf(missing, sizeof(missing), "%s/absent.txt", dir);
    CHECK(mkdir(dir, 0700) == 0);

    /* 10000 bytes with embedded NULs: exercises the grow path and pins that the
     * reader keeps the BYTE COUNT (no strlen truncation at the first NUL). */
    enum { SIZE = 10000 };
    FILE* f = fopen(file, "wb");
    CHECK(f);
    for (int i = 0; i < SIZE; i++) fputc((i % 7 == 0) ? 0 : 'a' + (i % 26), f);
    fclose(f);

    /* slurp */
    int64_t text = rt_file_read_text(T(file));
    CHECK(text != 3);
    CHECK(rt_string_len(text) == SIZE);
    CHECK(rt_string_data(text)[0] == 0 && rt_string_data(text)[1] == 'b');
    CHECK(rt_file_read_text(T(missing)) == 3);
    CHECK(rt_file_read_text(NULL, 5) == 3);

    /* stat twins */
    CHECK(rt_file_is_regular_no_follow(T(file)) == true);
    CHECK(rt_file_is_regular_no_follow(T(dir)) == false);
    CHECK(rt_file_is_regular_no_follow(T(missing)) == false);
    CHECK(rt_file_is_regular_no_follow(NULL, 3) == false);
    CHECK(symlink(file, link_path) == 0);
    CHECK(rt_file_is_regular_no_follow(T(link_path)) == false); /* no-follow */
    CHECK(rt_file_is_char_device(T("/dev/null")) == 1);
    CHECK(rt_file_is_char_device(T(file)) == 0);
    CHECK(rt_file_is_char_device(T(missing)) == 0);
    CHECK(rt_file_is_char_device(NULL, 3) == 0);

    /* fsync worker: file, directory (parent-dir idiom), missing, bad arg */
    CHECK(rt_file_fsync(T(file)) == 1);
    CHECK(rt_file_fsync(T(dir)) == 1);
    CHECK(rt_file_fsync(T(missing)) == 0);
    CHECK(rt_file_fsync(NULL, 3) == 0);

    /* probe lifecycle around a real facade probe: 2 total, 1 failed */
    int64_t token = rt_file_exists_probe_begin();
    CHECK(token > 0);
    CHECK(rt_file_exists(T(file)) == true);
    CHECK(rt_file_exists(T(missing)) == false);
    int64_t packed = rt_file_exists_probe_end(token);
    CHECK((packed >> 32) == 2 && (packed & 0xffffffff) == 1);
    CHECK(rt_file_exists_probe_end(token) == -2);

    unlink(link_path); unlink(file); rmdir(dir);
    printf("PASS rt_file_io_twins\n");
    return 0;
}
#endif /* !_WIN32 && !SIMPLE_TEST_CORE_RUNTIME */
