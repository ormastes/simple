/* runtime_dynload_snapshot_private.h -- Linux memfd snapshot of a provider
 * library, shared by runtime_dynload.c (owner) and runtime_native.c (the
 * !SIMPLE_RUNTIME_DYNLOAD_OWNER fallback copy of spl_dynlib_snapshot_linux).
 *
 * Not a public header: include it once per translation unit, after <errno.h>,
 * <fcntl.h>, <stdint.h>, <sys/stat.h>, <sys/syscall.h>, <linux/memfd.h> and
 * <unistd.h>. Everything here is static; it is empty off Linux.
 *
 * The two includers differ only in how they decode the path argument
 * (owner: borrowed rt_interp_cstr; fallback: rt_text_cstr_dup + free) and in
 * the fd-floor lock they take afterwards, so the shared part is exactly the
 * copy-and-seal step below. runtime_dynload.c's GPU-provider admission path
 * (simple_gpu_snapshot_linux_v1) is the third caller, under its own memfd name.
 * Pinned by src/runtime/test/rt_dynload_snapshot_private_selfcheck.c.
 */
#ifndef SIMPLE_RUNTIME_DYNLOAD_SNAPSHOT_PRIVATE_H
#define SIMPLE_RUNTIME_DYNLOAD_SNAPSHOT_PRIVATE_H

#if defined(__linux__)
#define SIMPLE_DYNLOAD_SNAPSHOT_MAX_BYTES UINT64_C(1073741824)

/* Copies the regular file at `path` (no symlink follow, <= 1 GiB) into a fresh
 * memfd named `memfd_name` (visible only in /proc) and seals it against
 * write/grow/shrink/reseal. Returns the memfd, or -1 with no fd leaked.
 * Rewound to offset 0. */
static int simple_dynload_snapshot_memfd_linux_v1(const char* path,
                                                  const char* memfd_name) {
    int source = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (source < 0) return -1;
    struct stat source_stat;
    if (fstat(source, &source_stat) != 0 || !S_ISREG(source_stat.st_mode) ||
        source_stat.st_size < 0 ||
        (uint64_t)source_stat.st_size > SIMPLE_DYNLOAD_SNAPSHOT_MAX_BYTES) {
        close(source);
        return -1;
    }
    int snapshot = (int)syscall(SYS_memfd_create, memfd_name,
                                MFD_CLOEXEC | MFD_ALLOW_SEALING);
    if (snapshot < 0) { close(source); return -1; }
    uint8_t buffer[65536];
    uint64_t total = 0;
    for (;;) {
        ssize_t got = read(source, buffer, sizeof(buffer));
        if (got == 0) break;
        if (got < 0) {
            if (errno == EINTR) continue;
            close(source); close(snapshot); return -1;
        }
        if ((uint64_t)got > SIMPLE_DYNLOAD_SNAPSHOT_MAX_BYTES - total) {
            close(source); close(snapshot); return -1;
        }
        total += (uint64_t)got;
        ssize_t offset = 0;
        while (offset < got) {
            ssize_t put = write(snapshot, buffer + offset, (size_t)(got - offset));
            if (put < 0 && errno == EINTR) continue;
            if (put <= 0) { close(source); close(snapshot); return -1; }
            offset += put;
        }
    }
    if (total != (uint64_t)source_stat.st_size || close(source) != 0 ||
        lseek(snapshot, 0, SEEK_SET) < 0 ||
        fcntl(snapshot, F_ADD_SEALS,
              F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL) != 0) {
        close(snapshot);
        return -1;
    }
    return snapshot;
}
#endif /* __linux__ */

#endif /* SIMPLE_RUNTIME_DYNLOAD_SNAPSHOT_PRIVATE_H */
