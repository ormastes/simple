/* Darwin owned executable snapshot. This is NOT a sealed executable pin.
 * Launch is path based: the guarantee requires trusted same-UID processes and
 * trusted ancestors of the private directory. A same-UID attacker can change
 * the file or its path between validation and posix_spawn's kernel lookup. */
#ifndef RUNTIME_SOSIX_DARWIN_IMAGE_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_IMAGE_PRIVATE_H
#ifdef __APPLE__
#include <CommonCrypto/CommonDigest.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <spawn.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <limits.h>

typedef struct {
    uint64_t generation;
    int fd;
    char directory[PATH_MAX];
    char path[PATH_MAX];
    unsigned char digest[CC_SHA256_DIGEST_LENGTH];
    dev_t device;
    ino_t inode;
} SosixDarwinImage;

static int sosix_darwin_image_hash(int fd, unsigned char digest[CC_SHA256_DIGEST_LENGTH]) {
    CC_SHA256_CTX ctx; unsigned char buffer[65536]; off_t offset = 0;
    CC_SHA256_Init(&ctx);
    for (;;) {
        ssize_t n = pread(fd, buffer, sizeof(buffer), offset);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) return errno;
        if (!n) break;
        CC_SHA256_Update(&ctx, buffer, (CC_LONG)n); offset += n;
    }
    CC_SHA256_Final(digest, &ctx); return 0;
}

static int sosix_darwin_image_create(int source_fd, SosixDarwinImage *image) {
    if (!image) return EINVAL;
    memset(image, 0, sizeof(*image)); image->fd = -1;
    struct stat source;
    if (fstat(source_fd, &source) || !S_ISREG(source.st_mode) || source.st_size <= 0)
        return errno ? errno : EINVAL;
    const char *base = getenv("TMPDIR"); if (!base || !*base) base = "/tmp";
    /* Spawn actions may change cwd before the kernel resolves the image path.
     * Keep the snapshot path absolute even when the caller uses TMPDIR=.. */
    char absolute_base[PATH_MAX];
    if (!realpath(base, absolute_base)) return errno;
    if (snprintf(image->directory, sizeof(image->directory), "%s/sosix-image-XXXXXXXX", absolute_base) >= (int)sizeof(image->directory)) return ENAMETOOLONG;
    if (!mkdtemp(image->directory)) return errno;
    if (snprintf(image->path, sizeof(image->path), "%s/image", image->directory) >= (int)sizeof(image->path)) { rmdir(image->directory); return ENAMETOOLONG; }
    int write_fd = open(image->path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (write_fd < 0) { int e = errno; rmdir(image->directory); return e; }
    int error = 0; unsigned char buffer[65536]; off_t offset = 0;
    while (offset < source.st_size) {
        size_t want = (size_t)(source.st_size - offset); if (want > sizeof(buffer)) want = sizeof(buffer);
        ssize_t n = pread(source_fd, buffer, want, offset);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { error = n < 0 ? errno : EIO; break; }
        ssize_t done = 0;
        while (done < n) {
            ssize_t w = write(write_fd, buffer + done, (size_t)(n - done));
            if (w < 0 && errno == EINTR) continue;
            if (w <= 0) { error = w < 0 ? errno : EIO; break; }
            done += w;
        }
        if (error) break;
        offset += n;
    }
    if (!error && fchmod(write_fd, 0500)) error = errno;
    if (close(write_fd) && !error) error = errno;
    if (!error) { image->fd = open(image->path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW); if (image->fd < 0) error = errno; }
    struct stat st;
    if (!error && (fstat(image->fd, &st) || !S_ISREG(st.st_mode))) error = errno ? errno : EIO;
    if (!error) { image->device = st.st_dev; image->inode = st.st_ino; error = sosix_darwin_image_hash(image->fd, image->digest); }
    if (error) { if (image->fd >= 0) close(image->fd); unlink(image->path); rmdir(image->directory); memset(image, 0, sizeof(*image)); image->fd = -1; return error; }
    do arc4random_buf(&image->generation, sizeof(image->generation)); while (!image->generation);
    return 0;
}

static int sosix_darwin_image_spawn(SosixDarwinImage *image, uint64_t generation, pid_t *pid,
        const posix_spawn_file_actions_t *actions, const posix_spawnattr_t *attributes,
        char *const argv[], char *const environment[]) {
    if (!image || !generation || image->generation != generation || image->fd < 0) return ESTALE;
    if (!pid || !argv || !environment) return EINVAL;
    struct stat st; unsigned char digest[CC_SHA256_DIGEST_LENGTH];
    if (lstat(image->path, &st)) return errno;
    if (!S_ISREG(st.st_mode) || st.st_dev != image->device || st.st_ino != image->inode) return ESTALE;
    int error = sosix_darwin_image_hash(image->fd, digest);
    if (error) return error;
    if (memcmp(digest, image->digest, sizeof(digest))) return ESTALE;
    return posix_spawn(pid, image->path, actions, attributes, argv, environment);
}

static int sosix_darwin_image_close(SosixDarwinImage *image, uint64_t generation) {
    if (!image || !generation || image->generation != generation || image->fd < 0) return ESTALE;
    int error = 0;
    if (close(image->fd)) error = errno;
    if (unlink(image->path) && !error) error = errno;
    if (rmdir(image->directory) && !error) error = errno;
    memset(image, 0, sizeof(*image)); image->fd = -1; return error;
}
#endif
#endif
