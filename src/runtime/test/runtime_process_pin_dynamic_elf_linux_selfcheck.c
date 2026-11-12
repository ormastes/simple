/* Linux owned-executable pin: admit a dynamically linked ELF executable in the
 * Darwin-parity class (main image sealed in a memfd and digest-bound; the
 * system loader and its shared libraries load unpinned), and refuse every
 * image that steers library resolution away from the system loader paths.
 *
 * Until this check rt_hal_static_elf_fd rejected PT_INTERP/PT_DYNAMIC, so the
 * Stage 2/3 compilers (dynamic, ld-linux + libc/libm/libstdc++/libgcc_s) never
 * started a profile HIR worker on Linux:
 *   [hir-shard] owner=0/2@0 reason: owned executable pin was rejected
 *
 * Run from the repository root. Compile WITHOUT -static: the test binary is
 * the dynamic image under test.
 *   cc -std=c11 -O0 -Wall -Wextra -pthread \
 *     src/runtime/test/runtime_process_pin_dynamic_elf_linux_selfcheck.c \
 *     -o /tmp/pin-dynamic-elf && /tmp/pin-dynamic-elf
 * Checks: (0) the reference SHA-256 passes a known-answer vector;
 * (1) the dynamic self image pins; (2) the owned digest equals the
 * SHA-256 of the file bytes; (3) the acquired sealed memfd fexecve()s and the
 * child runs under the system loader (its /proc/self/exe is the memfd);
 * (4) copies patched to carry DT_RUNPATH, DT_RPATH, no PT_INTERP, or a
 * PT_INTERP that is not a root-owned file are refused; (5) a directory with
 * the same path shape is still refused. */
#if !defined(__linux__)
#include <stdio.h>
int main(void) { puts("runtime_process_pin_dynamic_elf_linux_selfcheck: SKIP (requires Linux)"); return 77; }
#else
#define _GNU_SOURCE
#include "../runtime.h"
#include <assert.h>
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

/* Link stubs: the pin path touches none of these. */
SplArray* rt_array_new(int64_t capacity) {
    SplArray* a = calloc(1, sizeof(*a)); assert(a);
    a->cap = capacity > 0 ? capacity : 1;
    a->items = calloc((size_t)a->cap, sizeof(*a->items)); assert(a->items);
    return a;
}
int64_t rt_array_len(SplArray* a) { return a ? a->len : -1; }
int64_t rt_array_get(SplArray* a, int64_t i) { return a && i >= 0 && i < a->len ? a->items[i].as_int : 0; }
int8_t rt_array_push(SplArray* a, int64_t value) {
    if (!a || a->len >= a->cap) return 0;
    a->items[a->len++].as_int = value; return 1;
}
int8_t rt_array_set(SplArray* a, int64_t i, int64_t value) {
    if (!a || i < 0 || i >= a->len) return 0;
    a->items[i].as_int = value; return 1;
}
void rt_array_free(SplArray* a) { if (a) { free(a->items); free(a); } }
int64_t rt_value_int(int64_t value) { return value; }
int64_t rt_value_as_int(int64_t value) { return value; }
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t* rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_new(const uint8_t* bytes, uint64_t length) { (void)bytes; (void)length; return 1; }
int64_t rt_tuple_new(int64_t len) { return (int64_t)(uintptr_t)rt_array_new(len); }
int8_t rt_tuple_set(int64_t tuple, int64_t index, int64_t value) { return rt_array_set((SplArray*)(uintptr_t)tuple, index, value); }
int64_t rt_child_set_pdeathsig(int32_t signo) { (void)signo; return 0; }
void rt_fork_child_exit(int64_t exit_code) { _exit((int)exit_code); }
int64_t rt_fork_child_setup(void) { return -1; }
int64_t rt_fork_parent_peak_rss_bytes(void) { return 0; }
bool rt_fork_parent_signaled(void) { return false; }
const char* rt_fork_parent_stderr(void) { return ""; }
const char* rt_fork_parent_stdout(void) { return ""; }
bool rt_fork_parent_timed_out(void) { return false; }
int64_t rt_fork_parent_wait(int64_t child_pid, int64_t timeout_ms) { (void)child_pid; (void)timeout_ms; return -1; }
int64_t rt_fork_parent_wait_bounded(int64_t child_pid, int64_t timeout_ms, uint64_t max_output_bytes) {
    (void)child_pid; (void)timeout_ms; (void)max_output_bytes; return -1; }
int64_t simple_fork_child_setup_capture_v2(int64_t expires_at_unix_ms, int status_pipe[2]) {
    (void)expires_at_unix_ms; (void)status_pipe; return -1; }
int64_t simple_fork_parent_capture_flags_v1(void) { return 0; }
void simple_fork_parent_capture_lengths(uint64_t* out, uint64_t* err) { if (out) *out = 0; if (err) *err = 0; }
void simple_fork_parent_capture_release_v1(void) {}
int64_t simple_fork_parent_wait_bounded_bytes(int64_t child_pid, int64_t timeout_ms, uint64_t max_output_bytes) {
    (void)child_pid; (void)timeout_ms; (void)max_output_bytes; return -1; }
int simple_local_unix_origin_v1(void) { return 0; }
int simple_process_launch_admission_check_v1(int64_t expires_at_unix_ms) { (void)expires_at_unix_ms; return 0; }
int8_t rt_value_is_int(int64_t value) { (void)value; return 1; }
int64_t rt_free_deep(int64_t value) { (void)value; return 1; }
int64_t rt_array_bytes_validate(int64_t value) { (void)value; return -1; }
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t cap) {
    (void)value; (void)out; (void)cap; return -1; }
int64_t rt_proc_start_time(int64_t pid) { (void)pid; return -1; }

/* runtime_process.c keeps the raw-fd close/spawn; the pin itself (raw,
 * owned, acquire, digest) lives in runtime_process_owned.c, the TU the Rust
 * runtime crate -- and so every Stage 2 compiler -- actually links. This
 * harness defines _GNU_SOURCE; the crate does not, and the crate-lane test
 * env_process.rs::linux_owned_pin_tests covers that compilation mode. */
#include "../runtime_process.c"
#include "../runtime_process_owned.c"

static int failures = 0, checks = 0;
#define CHECK(cond, what) do { checks++; if (!(cond)) { fprintf(stderr, "FAIL: %s\n", what); failures++; } } while (0)

static char scratch[PATH_MAX / 2];
static char self_path[PATH_MAX];

/* Whole-file SHA-256 through the shared one-shot owned_sha256 (a different
 * padding path from the pin's streaming digest). Its block function is pinned
 * to the FIPS 180-2 "abc" vector by check (0); until 2026-11-13 this harness
 * hashed with the pin's own private block copy, whose round-constant table was
 * one entry short, so check (2) compared that wrong digest with itself. */
static int sha256_kat_abc(void) {
    static const uint8_t want[32] = {
        0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
        0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad};
    uint8_t got[32];
    owned_sha256((const uint8_t*)"abc", 3, got);
    return memcmp(got, want, sizeof(want)) == 0;
}
static int sha256_path(const char* path, uint8_t out[32]) {
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size <= 0) { close(fd); return 0; }
    uint8_t* bytes = malloc((size_t)st.st_size);
    if (!bytes) { close(fd); return 0; }
    off_t got = 0;
    while (got < st.st_size) {
        ssize_t n = read(fd, bytes + got, (size_t)(st.st_size - got));
        if (n <= 0) { free(bytes); close(fd); return 0; }
        got += n;
    }
    close(fd);
    owned_sha256(bytes, (size_t)st.st_size, out);
    free(bytes);
    return 1;
}

static int copy_self(const char* name, char out[PATH_MAX]) {
    snprintf(out, PATH_MAX, "%s/%s", scratch, name);
    int src = open(self_path, O_RDONLY | O_CLOEXEC);
    int dst = open(out, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0700);
    if (src < 0 || dst < 0) return 0;
    uint8_t buf[65536];
    for (;;) {
        ssize_t n = read(src, buf, sizeof(buf));
        if (n < 0) return 0;
        if (n == 0) break;
        if (write(dst, buf, (size_t)n) != n) return 0;
    }
    close(src); close(dst);
    return 1;
}

/* 64-bit little-endian ELF only (this host). Returns the phdr matching type. */
static int find_phdr(int fd, uint32_t type, Elf64_Phdr* out, off_t* at) {
    Elf64_Ehdr eh;
    if (pread(fd, &eh, sizeof(eh), 0) != (ssize_t)sizeof(eh)) return 0;
    for (Elf64_Half i = 0; i < eh.e_phnum; i++) {
        off_t off = (off_t)(eh.e_phoff + (Elf64_Off)i * sizeof(Elf64_Phdr));
        if (pread(fd, out, sizeof(*out), off) != (ssize_t)sizeof(*out)) return 0;
        if (out->p_type == type) { *at = off; return 1; }
    }
    return 0;
}

static int patch_first_dyn_tag(const char* path, Elf64_Sxword from, Elf64_Sxword to) {
    int fd = open(path, O_RDWR | O_CLOEXEC);
    if (fd < 0) return 0;
    Elf64_Phdr ph; off_t at;
    if (!find_phdr(fd, PT_DYNAMIC, &ph, &at)) { close(fd); return 0; }
    for (Elf64_Xword off = 0; off + sizeof(Elf64_Dyn) <= ph.p_filesz; off += sizeof(Elf64_Dyn)) {
        Elf64_Dyn d;
        if (pread(fd, &d, sizeof(d), (off_t)(ph.p_offset + off)) != (ssize_t)sizeof(d)) break;
        if (d.d_tag == DT_NULL) break;
        if (d.d_tag == from) {
            d.d_tag = to;
            int ok = pwrite(fd, &d, sizeof(d), (off_t)(ph.p_offset + off)) == (ssize_t)sizeof(d);
            close(fd); return ok;
        }
    }
    close(fd); return 0;
}

static int patch_phdr_type(const char* path, uint32_t from, uint32_t to) {
    int fd = open(path, O_RDWR | O_CLOEXEC);
    if (fd < 0) return 0;
    Elf64_Phdr ph; off_t at;
    if (!find_phdr(fd, from, &ph, &at)) { close(fd); return 0; }
    ph.p_type = to;
    int ok = pwrite(fd, &ph, sizeof(ph), at) == (ssize_t)sizeof(ph);
    close(fd); return ok;
}

/* Overwrite the PT_INTERP string with a shorter path (NUL padded). */
static int patch_interp(const char* path, const char* interp) {
    int fd = open(path, O_RDWR | O_CLOEXEC);
    if (fd < 0) return 0;
    Elf64_Phdr ph; off_t at;
    if (!find_phdr(fd, PT_INTERP, &ph, &at)) { close(fd); return 0; }
    size_t len = strlen(interp) + 1;
    if (len > ph.p_filesz) { close(fd); return 0; }
    char* bytes = calloc(1, ph.p_filesz);
    memcpy(bytes, interp, len);
    int ok = pwrite(fd, bytes, ph.p_filesz, (off_t)ph.p_offset) == (ssize_t)ph.p_filesz;
    free(bytes); close(fd); return ok;
}

static int run_pinned_child(int64_t owned, const char* argv0, char* out, size_t cap) {
    int fd = (int)rt_process_acquire_pinned_executable(owned);
    if (fd < 0) return -1;
    int pipefd[2];
    if (pipe(pipefd) != 0) { close(fd); return -1; }
    pid_t pid = fork();
    if (pid < 0) { close(fd); return -1; }
    if (pid == 0) {
        close(pipefd[0]);
        if (dup2(pipefd[1], STDOUT_FILENO) < 0) _exit(96);
        char* const argv[] = {(char*)argv0, (char*)"--pinned-child", NULL};
        char* const envp[] = {(char*)"PATH=/usr/bin:/bin", NULL};
        fexecve(fd, argv, envp);
        _exit(97);
    }
    close(pipefd[1]); close(fd);
    size_t used = 0;
    for (;;) {
        ssize_t n = read(pipefd[0], out + used, cap - 1 - used);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) break;
        used += (size_t)n;
        if (used >= cap - 1) break;
    }
    out[used] = '\0';
    close(pipefd[0]);
    int status = 0;
    if (waitpid(pid, &status, 0) != pid) return -1;
    return WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
}

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--pinned-child") == 0) {
        char exe[PATH_MAX];
        ssize_t n = readlink("/proc/self/exe", exe, sizeof(exe) - 1);
        if (n < 0) return 90;
        exe[n] = '\0';
        printf("OK %s\n", exe);
        return 0;
    }
    /* (0) The reference digest is real SHA-256. */
    CHECK(sha256_kat_abc(), "owned_sha256 matches the FIPS 180-2 abc vector");
    const char* base = getenv("TMPDIR");
    if (!base || !*base) base = "/tmp";
    snprintf(scratch, sizeof(scratch), "%s/pin-dynamic-elf-XXXXXX", base);
    if (!mkdtemp(scratch)) { perror("mkdtemp"); return 2; }

    /* The pin opens O_NOFOLLOW, so it takes the resolved image path, exactly
     * as the HIR owner passes the compiler's canonical path. */
    ssize_t self_len = readlink("/proc/self/exe", self_path, sizeof(self_path) - 1);
    if (self_len <= 0) { perror("readlink /proc/self/exe"); return 2; }
    self_path[self_len] = '\0';

    /* Precondition: this test binary is the dynamic class under test. */
    {
        int self = open(self_path, O_RDONLY | O_CLOEXEC);
        Elf64_Phdr ph; off_t at;
        CHECK(self >= 0 && find_phdr(self, PT_INTERP, &ph, &at), "test binary must be dynamically linked (do not pass -static)");
        if (self >= 0) close(self);
    }

    /* (1) The dynamic self image pins (raw contract and owned contract). */
    int64_t raw = rt_process_pin_executable(self_path);
    CHECK(raw >= 3, "rt_process_pin_executable admits a dynamic ELF executable");
    if (raw >= 3) {
        int seals = fcntl((int)raw, F_GET_SEALS);
        CHECK((seals & (F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL)) ==
              (F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL), "pinned memfd is fully sealed");
        CHECK(rt_process_close_pinned_executable(raw), "raw pin closes");
    }
    int64_t owned = rt_process_pin_executable_owned(self_path);
    CHECK(owned > 0, "rt_process_pin_executable_owned admits a dynamic ELF executable");

    /* (2) The owned digest is the SHA-256 of the file bytes (the closure
     * producer_digest the HIR owner compares against). */
    if (owned > 0) {
        uint8_t expected[32]; int hashed = sha256_path(self_path, expected);
        SplArray* digest = rt_process_pinned_executable_sha256_value(owned);
        int same = hashed && digest && rt_array_len(digest) == 32;
        for (int i = 0; same && i < 32; i++) same = rt_array_get(digest, i) == expected[i];
        CHECK(same, "owned pin digest equals SHA-256 of the file bytes");
        if (digest) rt_array_free(digest);
    }

    /* (3) The sealed memfd executes under the system loader. */
    if (owned > 0) {
        char out[PATH_MAX + 16];
        int rc = run_pinned_child(owned, argv[0], out, sizeof(out));
        CHECK(rc == 0, "pinned dynamic image runs to exit 0 via fexecve");
        CHECK(strncmp(out, "OK ", 3) == 0, "pinned child reported OK");
        CHECK(strstr(out, "memfd:") != NULL, "pinned child's /proc/self/exe is the memfd (not the path)");
        if (rc != 0 || strncmp(out, "OK ", 3) != 0) fprintf(stderr, "child rc=%d out=%s\n", rc, out);
        CHECK(rt_process_close_pinned_executable_owned(owned), "owned pin closes");
        CHECK(rt_process_acquire_pinned_executable(owned) < 0, "closed owned pin cannot be acquired");
    }

    /* (4) Fail closed: images that steer library resolution are refused. */
    char fixture[PATH_MAX];
    CHECK(copy_self("runpath", fixture) && patch_first_dyn_tag(fixture, DT_NEEDED, DT_RUNPATH), "fixture: DT_RUNPATH");
    CHECK(rt_process_pin_executable(fixture) < 0, "DT_RUNPATH image is refused");
    CHECK(rt_process_pin_executable_owned(fixture) <= 0, "DT_RUNPATH image is refused (owned)");
    CHECK(copy_self("rpath", fixture) && patch_first_dyn_tag(fixture, DT_NEEDED, DT_RPATH), "fixture: DT_RPATH");
    CHECK(rt_process_pin_executable(fixture) < 0, "DT_RPATH image is refused");
    CHECK(copy_self("nointerp", fixture) && patch_phdr_type(fixture, PT_INTERP, PT_NULL), "fixture: PT_DYNAMIC without PT_INTERP");
    CHECK(rt_process_pin_executable(fixture) < 0, "PT_DYNAMIC without PT_INTERP (static-pie / shared object shape) is refused");
    {
        /* A user-owned loader path short enough to fit the PT_INTERP slot. */
        char loader[64]; snprintf(loader, sizeof(loader), "/dev/shm/spl-pin-%d", (int)getpid());
        int lfd = open(loader, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0755);
        CHECK(lfd >= 0, "fixture: user-owned loader file");
        if (lfd >= 0) {
            close(lfd);
            CHECK(copy_self("userinterp", fixture) && patch_interp(fixture, loader), "fixture: PT_INTERP -> user-owned file");
            CHECK(rt_process_pin_executable(fixture) < 0, "PT_INTERP that is not a root-owned regular file is refused");
            unlink(loader);
        }
        CHECK(copy_self("missinginterp", fixture) && patch_interp(fixture, "/nonexistent/ld.so"), "fixture: PT_INTERP -> missing path");
        CHECK(rt_process_pin_executable(fixture) < 0, "PT_INTERP that does not exist is refused");
        CHECK(copy_self("relinterp", fixture) && patch_interp(fixture, "lib/ld-linux.so"), "fixture: relative PT_INTERP");
        CHECK(rt_process_pin_executable(fixture) < 0, "relative PT_INTERP is refused");
    }
    /* (5) Unchanged rejections: non-executable file and directory. */
    CHECK(copy_self("noexec", fixture) && chmod(fixture, 0600) == 0, "fixture: no exec bit");
    CHECK(rt_process_pin_executable(fixture) < 0, "non-executable file is refused");
    CHECK(rt_process_pin_executable(scratch) < 0, "directory is refused");

    /* Cleanup. */
    const char* names[] = {"runpath", "rpath", "nointerp", "userinterp", "missinginterp", "relinterp", "noexec"};
    for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); i++) {
        snprintf(fixture, sizeof(fixture), "%s/%s", scratch, names[i]); unlink(fixture);
    }
    rmdir(scratch);
    if (failures) { fprintf(stderr, "runtime_process_pin_dynamic_elf_linux_selfcheck: FAIL (%d of %d)\n", failures, checks); return 1; }
    printf("runtime_process_pin_dynamic_elf_linux_selfcheck: PASS (%d checks)\n", checks);
    return 0;
}
#endif
