#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#if !defined(O_DIRECTORY) || !defined(O_NOFOLLOW) || !defined(O_CLOEXEC) || !defined(AT_SYMLINK_NOFOLLOW)
#error "secure openat publication primitives unavailable"
#endif

static int same_dir(const char *path, const struct stat *expected) {
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    struct stat st;
    int ok = fd >= 0 && fstat(fd, &st) == 0 && st.st_dev == expected->st_dev && st.st_ino == expected->st_ino;
    if (fd >= 0) close(fd);
    return ok;
}

static int same_mtime(const struct stat *left, const struct stat *right) {
#if defined(__APPLE__)
    return left->st_mtimespec.tv_sec == right->st_mtimespec.tv_sec &&
        left->st_mtimespec.tv_nsec == right->st_mtimespec.tv_nsec;
#else
    return left->st_mtim.tv_sec == right->st_mtim.tv_sec &&
        left->st_mtim.tv_nsec == right->st_mtim.tv_nsec;
#endif
}

int main(int argc, char **argv) {
    if (argc != 4 || strchr(argv[3], '/') || !argv[3][0]) return 2;
    int dfd = open(argv[1], O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    int sfd = open(argv[2], O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    struct stat ds, ss, ss_after, existing;
    if (dfd < 0 || sfd < 0 || fstat(dfd, &ds) || fstat(sfd, &ss) ||
        !S_ISDIR(ds.st_mode) || ds.st_uid != geteuid() || (ds.st_mode & 0022) ||
        !S_ISREG(ss.st_mode) || ss.st_nlink != 1) return 2;
    int final_status = fstatat(dfd, argv[3], &existing, AT_SYMLINK_NOFOLLOW);
    if (final_status == 0 && (!S_ISREG(existing.st_mode) || existing.st_nlink != 1)) return 2;
    if (final_status != 0 && errno != ENOENT) return 2;
    unsigned char random_bytes[16];
    int random_fd = open("/dev/urandom", O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (random_fd < 0 || read(random_fd, random_bytes, sizeof(random_bytes)) != (ssize_t)sizeof(random_bytes)) return 2;
    close(random_fd);
    char tmp[96];
    snprintf(tmp, sizeof(tmp), ".mci-publish.%02x%02x%02x%02x%02x%02x%02x%02x",
        random_bytes[0], random_bytes[1], random_bytes[2], random_bytes[3],
        random_bytes[4], random_bytes[5], random_bytes[6], random_bytes[7]);
    int tfd = openat(dfd, tmp, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (tfd < 0) return 2;
    struct stat ts;
    if (fstat(tfd, &ts) || !S_ISREG(ts.st_mode) || ts.st_nlink != 1) goto fail;
    char buf[16384]; ssize_t n;
    while ((n = read(sfd, buf, sizeof(buf))) > 0) {
        ssize_t off = 0;
        while (off < n) { ssize_t w = write(tfd, buf + off, (size_t)(n - off)); if (w <= 0) goto fail; off += w; }
    }
    if (n < 0 || fstat(sfd, &ss_after) || ss_after.st_dev != ss.st_dev || ss_after.st_ino != ss.st_ino ||
        ss_after.st_size != ss.st_size || !same_mtime(&ss_after, &ss) ||
        fsync(tfd) || close(tfd)) { tfd = -1; goto fail; }
    tfd = -1;
#ifdef TEST_ONLY
    if (!strcmp(argv[3], "__test_dir_swap__")) {
        char moved[4096]; snprintf(moved, sizeof(moved), "%s.old", argv[1]);
        if (rename(argv[1], moved) || mkdir(argv[1], 0700)) goto fail;
    }
#endif
    if (!same_dir(argv[1], &ds)) goto fail;
    /* linkat is an atomic no-replace publish; an existing final always fails. */
    if (linkat(dfd, tmp, dfd, argv[3], 0)) goto fail;
    if (!same_dir(argv[1], &ds)) { unlinkat(dfd, argv[3], 0); goto fail; }
    if (unlinkat(dfd, tmp, 0)) { unlinkat(dfd, argv[3], 0); goto fail; }
#ifdef TEST_ONLY
    if (!strcmp(argv[3], "__test_fsync_fail__")) { close(sfd); close(dfd); return 3; }
#endif
    if (fsync(dfd)) { close(sfd); close(dfd); return 3; }
    close(sfd); close(dfd); return 0;
fail:
    if (tfd >= 0) close(tfd);
    unlinkat(dfd, tmp, 0); close(sfd); close(dfd); return 2;
}
