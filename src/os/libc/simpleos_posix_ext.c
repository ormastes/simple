/*
 * simpleos_posix_ext.c — POSIX functions the Simple runtime needs that the
 * SimpleOS kernel has no dedicated syscall for.
 *
 * SimpleOS syscall table (src/os/kernel/ipc/syscall.spl) provides
 * 31=Read, 32=Write, 46=Lseek but NO pread/pwrite. They are therefore built
 * from seek+io with the file offset saved and restored, which is a real
 * implementation of the required behaviour on a single-threaded caller.
 *
 * KNOWN LIMITATION, stated rather than hidden: POSIX pread/pwrite are atomic
 * with respect to the file offset. This seek-based version is not. If two
 * threads share one fd, a concurrent read/write can observe the temporarily
 * moved offset. Fixing that properly needs a real pread/pwrite syscall; see
 * the tracking note in
 * doc/08_tracking/bug/simpleos_payload_link_missing_20_rt_symbols_2026-08-06.md
 */

#include "include/unistd.h"
#include "include/stdio.h"
#include "include/string.h"
#include "include/ctype.h"
#include "include/errno.h"
#include "include/stdint.h"

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);

ssize_t pread(int fd, void *buf, size_t count, off_t offset) {
    if (!buf) { errno = EFAULT; return -1; }
    if (offset < 0) { errno = EINVAL; return -1; }

    off_t saved = lseek(fd, 0, SEEK_CUR);
    if (saved < 0) return -1;
    if (lseek(fd, offset, SEEK_SET) < 0) return -1;

    ssize_t n = read(fd, buf, count);
    int saved_errno = errno;

    /* Always restore the offset, even on a failed read. */
    if (lseek(fd, saved, SEEK_SET) < 0 && n >= 0) return -1;

    if (n < 0) errno = saved_errno;
    return n;
}

ssize_t pwrite(int fd, const void *buf, size_t count, off_t offset) {
    if (!buf) { errno = EFAULT; return -1; }
    if (offset < 0) { errno = EINVAL; return -1; }

    off_t saved = lseek(fd, 0, SEEK_CUR);
    if (saved < 0) return -1;
    if (lseek(fd, offset, SEEK_SET) < 0) return -1;

    ssize_t n = write(fd, buf, count);
    int saved_errno = errno;

    if (lseek(fd, saved, SEEK_SET) < 0 && n >= 0) return -1;

    if (n < 0) errno = saved_errno;
    return n;
}

/*
 * fsync / fdatasync — report ENOSYS rather than falsely claim durability.
 *
 * This is the deliberate, evidence-based choice. Returning 0 would tell the
 * caller its data is safely on stable storage. On SimpleOS today it is not,
 * for two independent reasons found by tracing write(2) from
 * src/os/kernel/ipc/syscall.spl:413 down to the NVMe driver:
 *
 *  1. The FAT32 file size is never written back to the directory entry.
 *     fat32_write (src/lib/nogc_async_mut/fs_driver/fat32_core.spl:1478)
 *     updates only the in-memory open-file record, and fat32_close does not
 *     touch the dirent either — so after write+close the on-disk entry still
 *     reads size 0. No `_write_u32_le`-style dirent writeback exists.
 *  2. The device's volatile write cache is never flushed. BlockDevice
 *     (src/lib/nogc_sync_mut/fs_driver/block_device.spl) exposes no flush, and
 *     although the NVMe driver implements FLUSH (opcode 0x00), it is
 *     unreachable from the filesystem path.
 *
 * FileSync syscall 78 now orders FAT32 directory-entry writeback before the
 * mounted BlockDevice.flush operation. Unsupported devices fail closed; the
 * libc boundary never fabricates durability.
 */
int fsync(int fd) {
    if (fd < 0) { errno = EBADF; return -1; }
    long rc = simpleos_syscall(78, (long)fd, 0, 0, 0, 0);
    if (rc < 0) { errno = (int)-rc; return -1; }
    return 0;
}

int fdatasync(int fd) {
    return fsync(fd);
}

/*
 * strcasestr — case-insensitive substring search (GNU extension).
 * Pure string code, no kernel involvement, so this is exact.
 */
char *strcasestr(const char *haystack, const char *needle) {
    if (!haystack || !needle) return NULL;
    if (!*needle) return (char *)haystack;

    for (const char *h = haystack; *h; h++) {
        const char *a = h;
        const char *b = needle;
        while (*a && *b &&
               tolower((unsigned char)*a) == tolower((unsigned char)*b)) {
            a++; b++;
        }
        if (!*b) return (char *)h;
    }
    return NULL;
}
