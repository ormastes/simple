#ifndef SIMPLE_RUNTIME_SOSIX_FREEBSD_IMAGE_V1_H
#define SIMPLE_RUNTIME_SOSIX_FREEBSD_IMAGE_V1_H

/* Private staging primitive, not launch admission. The result is a read-only
 * descriptor for an unlinked regular vnode; the caller owns and closes it.
 * This is FILE backing, not a sealed memory image. The process provider must
 * still authenticate the bytes and enforce its complete launch policy. */
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#if defined(__FreeBSD__)
#include <fcntl.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>
#endif

static int sosix_freebsd_stage_image_v1(const uint8_t *bytes, size_t len) {
    if (!bytes || len == 0 || len > 64U * 1024U * 1024U) {
        errno = EINVAL;
        return -1;
    }
#if !defined(__FreeBSD__)
    errno = ENOTSUP;
    return -1;
#else
    char directory[] = "/tmp/simple-sosix-image-XXXXXXXXXX";
    if (!mkdtemp(directory)) return -1;
    char path[sizeof(directory) + 8];
    if (snprintf(path, sizeof(path), "%s/image", directory) < 0) {
        rmdir(directory); errno = EIO; return -1;
    }
    int writer = open(path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (writer < 0) { int e = errno; rmdir(directory); errno = e; return -1; }
    int reader = -1, saved = 0;
    struct stat before, after;
    size_t at = 0;
    if (fcntl(writer, F_SETFD, FD_CLOEXEC) < 0) goto fail;
    while (at < len) {
        ssize_t n = write(writer, bytes + at, len - at);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { if (n == 0) errno = EIO; goto fail; }
        at += (size_t)n;
    }
    if (fchmod(writer, 0500) < 0 || fstat(writer, &before) < 0 ||
        !S_ISREG(before.st_mode) || before.st_size != (off_t)len) goto fail;
    reader = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (reader < 0 || fstat(reader, &after) < 0) goto fail;
    if (!S_ISREG(after.st_mode) || before.st_dev != after.st_dev ||
        before.st_ino != after.st_ino || after.st_size != before.st_size) {
        errno = ESTALE; goto fail;
    }
    if (unlink(path) < 0) goto fail;
    path[0] = '\0';
    if (rmdir(directory) < 0) goto fail;
    if (close(writer) < 0) { writer = -1; goto fail; }
    return reader;
fail:
    saved = errno;
    if (reader >= 0) close(reader);
    if (writer >= 0) close(writer);
    if (path[0]) unlink(path);
    rmdir(directory);
    errno = saved;
    return -1;
#endif
}
#endif
