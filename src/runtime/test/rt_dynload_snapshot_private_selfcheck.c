/*
 * Characterization selfcheck for runtime_dynload_snapshot_private.h, the Linux
 * memfd copy-and-seal step shared by runtime_dynload.c (owner) and the
 * !SIMPLE_RUNTIME_DYNLOAD_OWNER fallback in runtime_native.c.
 *
 * Linux only (memfd_create + F_ADD_SEALS). On any other host it compiles to a
 * program that reports SKIP and exits 0; the check script only counts a Linux
 * run as evidence.
 *
 *   clang -O1 -I src/runtime src/runtime/test/rt_dynload_snapshot_private_selfcheck.c -o sc && ./sc
 */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE /* F_ADD_SEALS / F_GET_SEALS; must precede the first include */
#endif
#include <stdio.h>

#if defined(__linux__)
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <linux/memfd.h>
#include <unistd.h>

#include "runtime_dynload_snapshot_private.h"

static int failures = 0;

static void expect(const char *what, int ok)
{
    if (!ok) { printf("FAIL %s\n", what); failures++; }
}

int main(void)
{
    /* Honour TMPDIR: some hosts (e.g. a WSL guest in disk-recovery mode) have a
     * read-only /tmp, and a fixture that cannot be written is a FAIL, not a skip. */
    const char *tmp = getenv("TMPDIR");
    char dir[512];
    snprintf(dir, sizeof(dir), "%s/simple-dynload-snapshot-XXXXXX",
             (tmp && tmp[0]) ? tmp : "/tmp");
    if (!mkdtemp(dir)) { printf("FAIL mkdtemp %s: %s\n", dir, strerror(errno)); return 1; }
    char path[512];
    snprintf(path, sizeof(path), "%s/provider.so", dir);

    /* 70000 bytes: crosses the 64 KiB copy buffer so the loop runs twice. */
    const size_t len = 70000;
    unsigned char *payload = malloc(len);
    for (size_t i = 0; i < len; ++i) payload[i] = (unsigned char)(i * 7 + 3);
    FILE *f = fopen(path, "wb");
    expect("write fixture", f && fwrite(payload, 1, len, f) == len && fclose(f) == 0);

    int fd = simple_dynload_snapshot_memfd_linux_v1(path, "simple-selfcheck");
    expect("snapshot of regular file succeeds", fd >= 0);
    if (fd >= 0) {
        struct stat st;
        expect("snapshot fstat", fstat(fd, &st) == 0);
        expect("snapshot has source size", (uint64_t)st.st_size == len);
        expect("snapshot rewound to 0", lseek(fd, 0, SEEK_CUR) == 0);
        unsigned char *back = malloc(len);
        size_t got = 0;
        while (got < len) {
            ssize_t r = read(fd, back + got, len - got);
            if (r <= 0) break;
            got += (size_t)r;
        }
        expect("snapshot bytes identical", got == len && memcmp(back, payload, len) == 0);
        int seals = fcntl(fd, F_GET_SEALS);
        expect("snapshot sealed write|grow|shrink|seal",
               seals >= 0 && (seals & (F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL))
                             == (F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL));
        expect("sealed snapshot rejects write", write(fd, "x", 1) < 0 && errno == EPERM);
        free(back);
        close(fd);
    }

    /* Rejections: a directory, a missing path, and a symlink (O_NOFOLLOW). */
    expect("directory rejected", simple_dynload_snapshot_memfd_linux_v1(dir, "simple-selfcheck") == -1);
    snprintf(path, sizeof(path), "%s/missing.so", dir);
    expect("missing path rejected", simple_dynload_snapshot_memfd_linux_v1(path, "simple-selfcheck") == -1);
    char link[512];
    snprintf(link, sizeof(link), "%s/link.so", dir);
    snprintf(path, sizeof(path), "%s/provider.so", dir);
    expect("symlink fixture", symlink(path, link) == 0);
    expect("symlink rejected", simple_dynload_snapshot_memfd_linux_v1(link, "simple-selfcheck") == -1);

    /* No fd leaked by the rejection paths: the next fd is the one we expect. */
    int probe_a = open("/dev/null", O_RDONLY);
    close(probe_a);
    (void)simple_dynload_snapshot_memfd_linux_v1(dir, "simple-selfcheck");
    (void)simple_dynload_snapshot_memfd_linux_v1(link, "simple-selfcheck");
    int probe_b = open("/dev/null", O_RDONLY);
    expect("rejection paths leak no fd", probe_a == probe_b);
    close(probe_b);

    unlink(link); unlink(path); rmdir(dir); free(payload);
    printf("dynload snapshot private selfcheck: %s\n", failures == 0 ? "PASS" : "FAIL");
    return failures == 0 ? 0 : 1;
}
#else
int main(void)
{
    printf("dynload snapshot private selfcheck: SKIP (not Linux)\n");
    return 0;
}
#endif
