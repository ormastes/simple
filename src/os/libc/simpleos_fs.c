/*
 * SimpleOS Filesystem Operations
 *
 * Implements stat, directory ops, FILE stream I/O, path operations,
 * and miscellaneous POSIX file functions on top of SimpleOS syscalls.
 *
 * Syscall numbers (from src/os/kernel/ipc/syscall.spl):
 *   30  = Open         31  = Read          32  = Write         33  = Close
 *   34  = Stat         35  = Mkdir         36  = Readdir
 *   39  = Unlink       43  = Ftruncate     44  = Rename
 *   45  = Rmdir        46  = Lseek         47  = Getcwd
 *   48  = Chdir
 */

#include "include/stdio.h"
#include "include/sys/stat.h"
#include "include/dirent.h"
#include "include/fcntl.h"
#include "include/errno.h"
#include "include/string.h"
#include "include/stdlib.h"
#include "include/unistd.h"

/* ====================================================================
 * Syscall interface
 * ==================================================================== */

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                 int64_t a2, int64_t a3, int64_t a4);
extern int errno;

/* ====================================================================
 * FILE struct definition
 *
 * The opaque FILE type (struct __simpleos_FILE) is defined here with
 * additional fields beyond the minimal {fd} in simpleos_libc.c.
 * The existing stdin/stdout/stderr from simpleos_libc.c only use the
 * fd field (which is at offset 0), so they remain compatible.
 * ==================================================================== */

struct __simpleos_FILE {
    int fd;
    int eof;
    int error;
    int mode;
};

/* ====================================================================
 * 1. stat family
 * ==================================================================== */

int stat(const char *path, struct stat *buf) {
    int64_t r = simpleos_syscall(34, (int64_t)path, (int64_t)strlen(path),
                                  (int64_t)buf, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int fstat(int fd, struct stat *buf) {
    /* arg3=1 signals fd-mode to the kernel (SimpleOS doesn't distinguish yet) */
    int64_t r = simpleos_syscall(34, (int64_t)fd, 0, (int64_t)buf, 1, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int lstat(const char *path, struct stat *buf) {
    /* No symlinks in SimpleOS — fall through to stat */
    return stat(path, buf);
}

/* ====================================================================
 * 2. Directory operations
 * ==================================================================== */

struct _DIR_impl {
    int fd;
    struct dirent entry;
    int eof;
};

DIR *opendir(const char *name) {
    int fd = (int)simpleos_syscall(30, (int64_t)name, (int64_t)strlen(name),
                                    O_RDONLY, 0, 0);
    if (fd < 0) { errno = (int)(-fd); return NULL; }

    struct _DIR_impl *d = (struct _DIR_impl *)malloc(sizeof(struct _DIR_impl));
    if (!d) {
        simpleos_syscall(33, fd, 0, 0, 0, 0);
        errno = ENOMEM;
        return NULL;
    }
    d->fd  = fd;
    d->eof = 0;
    return (DIR *)d;
}

struct dirent *readdir(DIR *dirp) {
    struct _DIR_impl *d = (struct _DIR_impl *)dirp;
    if (d->eof) return NULL;

    int64_t r = simpleos_syscall(36, d->fd, (int64_t)&d->entry,
                                  (int64_t)sizeof(struct dirent), 0, 0);
    if (r <= 0) {
        d->eof = 1;
        return NULL;
    }
    return &d->entry;
}

int closedir(DIR *dirp) {
    struct _DIR_impl *d = (struct _DIR_impl *)dirp;
    int fd = d->fd;
    free(d);
    int64_t r = simpleos_syscall(33, fd, 0, 0, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

void rewinddir(DIR *dirp) {
    struct _DIR_impl *d = (struct _DIR_impl *)dirp;
    /* Seek directory fd back to beginning */
    simpleos_syscall(46, d->fd, 0, SEEK_SET, 0, 0);
    d->eof = 0;
}

/* ====================================================================
 * 3. FILE stream operations
 * ==================================================================== */

FILE *fopen(const char *path, const char *mode) {
    int flags = 0;

    if (strcmp(mode, "r") == 0 || strcmp(mode, "rb") == 0)
        flags = O_RDONLY;
    else if (strcmp(mode, "w") == 0 || strcmp(mode, "wb") == 0)
        flags = O_WRONLY | O_CREAT | O_TRUNC;
    else if (strcmp(mode, "a") == 0 || strcmp(mode, "ab") == 0)
        flags = O_WRONLY | O_CREAT | O_APPEND;
    else if (strcmp(mode, "r+") == 0 || strcmp(mode, "rb+") == 0 ||
             strcmp(mode, "r+b") == 0)
        flags = O_RDWR;
    else if (strcmp(mode, "w+") == 0 || strcmp(mode, "wb+") == 0 ||
             strcmp(mode, "w+b") == 0)
        flags = O_RDWR | O_CREAT | O_TRUNC;
    else if (strcmp(mode, "a+") == 0 || strcmp(mode, "ab+") == 0 ||
             strcmp(mode, "a+b") == 0)
        flags = O_RDWR | O_CREAT | O_APPEND;
    else {
        errno = EINVAL;
        return NULL;
    }

    int fd = (int)simpleos_syscall(30, (int64_t)path, (int64_t)strlen(path),
                                    flags, 0644, 0);
    if (fd < 0) { errno = (int)(-fd); return NULL; }

    FILE *fp = (FILE *)malloc(sizeof(struct __simpleos_FILE));
    if (!fp) {
        simpleos_syscall(33, fd, 0, 0, 0, 0);
        errno = ENOMEM;
        return NULL;
    }
    fp->fd    = fd;
    fp->eof   = 0;
    fp->error = 0;
    fp->mode  = flags;
    return fp;
}

int fclose(FILE *fp) {
    if (!fp) return EOF;
    int fd = fp->fd;
    free(fp);
    int64_t r = simpleos_syscall(33, fd, 0, 0, 0, 0);
    return r < 0 ? EOF : 0;
}

size_t fread(void *buf, size_t size, size_t nmemb, FILE *fp) {
    if (!fp || size == 0 || nmemb == 0) return 0;
    size_t total = size * nmemb;
    int64_t r = simpleos_syscall(31, fp->fd, (int64_t)buf, (int64_t)total, 0, 0);
    if (r <= 0) {
        if (r == 0) fp->eof = 1;
        else        fp->error = 1;
        return 0;
    }
    return (size_t)r / size;
}

size_t fwrite(const void *buf, size_t size, size_t nmemb, FILE *fp) {
    if (!fp || size == 0 || nmemb == 0) return 0;
    size_t total = size * nmemb;
    int64_t r = simpleos_syscall(32, fp->fd, (int64_t)buf, (int64_t)total, 0, 0);
    if (r < 0) {
        fp->error = 1;
        return 0;
    }
    return (size_t)r / size;
}

int fseek(FILE *fp, long offset, int whence) {
    if (!fp) { errno = EBADF; return -1; }
    int64_t r = simpleos_syscall(46, fp->fd, (int64_t)offset, whence, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    fp->eof = 0;
    return 0;
}

long ftell(FILE *fp) {
    if (!fp) { errno = EBADF; return -1; }
    int64_t r = simpleos_syscall(46, fp->fd, 0, SEEK_CUR, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return (long)r;
}

void rewind(FILE *fp) {
    if (fp) {
        fseek(fp, 0, SEEK_SET);
        fp->error = 0;
    }
}

int fflush(FILE *fp) {
    /* No buffering in SimpleOS libc */
    (void)fp;
    return 0;
}

int feof(FILE *fp) {
    return fp ? fp->eof : 0;
}

int ferror(FILE *fp) {
    return fp ? fp->error : 0;
}

void clearerr(FILE *fp) {
    if (fp) {
        fp->eof   = 0;
        fp->error = 0;
    }
}

int fileno(FILE *fp) {
    return fp ? fp->fd : -1;
}

char *fgets(char *s, int n, FILE *fp) {
    if (!fp || n <= 0) return NULL;
    int i = 0;
    while (i < n - 1) {
        char c;
        int64_t r = simpleos_syscall(31, fp->fd, (int64_t)&c, 1, 0, 0);
        if (r <= 0) {
            if (r == 0 && i == 0) { fp->eof = 1; return NULL; }
            if (r < 0)  { fp->error = 1; if (i == 0) return NULL; }
            break;
        }
        s[i++] = c;
        if (c == '\n') break;
    }
    s[i] = '\0';
    return s;
}

int fgetc(FILE *fp) {
    if (!fp) return EOF;
    unsigned char c;
    int64_t r = simpleos_syscall(31, fp->fd, (int64_t)&c, 1, 0, 0);
    if (r <= 0) {
        if (r == 0) fp->eof = 1;
        else        fp->error = 1;
        return EOF;
    }
    return (int)c;
}

int getc(FILE *fp) {
    return fgetc(fp);
}

int getchar(void) {
    return fgetc(stdin);
}

int ungetc(int c, FILE *fp) {
    /* No buffer to push back into — not supported */
    (void)fp;
    (void)c;
    errno = ENOSYS;
    return EOF;
}

int putc(int c, FILE *fp) {
    return fputc(c, fp);
}

int putchar(int c) {
    return fputc(c, stdout);
}

/* ====================================================================
 * 4. Path and file management operations
 * ==================================================================== */

int remove(const char *path) {
    int64_t r = simpleos_syscall(39, (int64_t)path, (int64_t)strlen(path),
                                  0, 0, 0); /* Unlink */
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int rename(const char *oldpath, const char *newpath) {
    int64_t r = simpleos_syscall(44, (int64_t)oldpath, (int64_t)strlen(oldpath),
                                      (int64_t)newpath, (int64_t)strlen(newpath), 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

char *getcwd(char *buf, size_t size) {
    int64_t r = simpleos_syscall(47, (int64_t)buf, (int64_t)size, 0, 0, 0);
    if (r < 0) { errno = (int)(-r); return NULL; }
    return buf;
}

int chdir(const char *path) {
    int64_t r = simpleos_syscall(48, (int64_t)path, (int64_t)strlen(path),
                                  0, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int mkdir(const char *path, mode_t mode) {
    int64_t r = simpleos_syscall(35, (int64_t)path, (int64_t)strlen(path),
                                  (int64_t)mode, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int rmdir(const char *path) {
    int64_t r = simpleos_syscall(45, (int64_t)path, (int64_t)strlen(path),
                                  0, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int unlink(const char *path) {
    return remove(path);
}

/* ====================================================================
 * 5. Low-level POSIX file operations
 * ==================================================================== */

off_t lseek(int fd, off_t offset, int whence) {
    int64_t r = simpleos_syscall(46, fd, (int64_t)offset, whence, 0, 0);
    if (r < 0) { errno = (int)(-r); return (off_t)-1; }
    return (off_t)r;
}

int ftruncate(int fd, off_t length) {
    int64_t r = simpleos_syscall(43, fd, (int64_t)length, 0, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int dup(int oldfd) {
    /* No kernel dup syscall yet */
    (void)oldfd;
    errno = ENOSYS;
    return -1;
}

int dup2(int oldfd, int newfd) {
    /* No kernel dup2 syscall yet */
    (void)oldfd;
    (void)newfd;
    errno = ENOSYS;
    return -1;
}

int pipe(int pipefd[2]) {
    /* No kernel pipe syscall yet */
    (void)pipefd;
    errno = ENOSYS;
    return -1;
}

int fcntl(int fd, int cmd, ...) {
    /* No kernel fcntl syscall yet */
    (void)fd;
    (void)cmd;
    errno = ENOSYS;
    return -1;
}

int access(const char *path, int mode) {
    /* Try stat — if it succeeds the file exists. Mode checks not yet
     * enforced by SimpleOS kernel, so existence is all we verify. */
    (void)mode;
    struct stat st;
    return stat(path, &st);
}

/* ====================================================================
 * 6. Misc stubs
 * ==================================================================== */

int chmod(const char *path, mode_t mode) {
    /* No chmod syscall yet */
    (void)path;
    (void)mode;
    errno = ENOSYS;
    return -1;
}

int isatty(int fd) {
    /* fd 0/1/2 are the console in SimpleOS */
    return (fd >= 0 && fd <= 2) ? 1 : 0;
}

void perror(const char *s) {
    if (s && *s) {
        size_t len = strlen(s);
        write(2, s, len);
        write(2, ": ", 2);
    }
    /* Minimal error string table */
    const char *msg;
    switch (errno) {
    case 0:       msg = "Success"; break;
    case EPERM:   msg = "Operation not permitted"; break;
    case ENOENT:  msg = "No such file or directory"; break;
    case EIO:     msg = "I/O error"; break;
    case EBADF:   msg = "Bad file descriptor"; break;
    case ENOMEM:  msg = "Out of memory"; break;
    case EACCES:  msg = "Permission denied"; break;
    case EEXIST:  msg = "File exists"; break;
    case ENOTDIR: msg = "Not a directory"; break;
    case EINVAL:  msg = "Invalid argument"; break;
    case ENOSYS:  msg = "Function not implemented"; break;
    case ENOSPC:  msg = "No space left on device"; break;
    default:      msg = "Unknown error"; break;
    }
    write(2, msg, strlen(msg));
    write(2, "\n", 1);
}

FILE *tmpfile(void) {
    errno = ENOSYS;
    return NULL;
}

char *tmpnam(char *s) {
    (void)s;
    errno = ENOSYS;
    return NULL;
}

FILE *freopen(const char *path, const char *mode, FILE *stream) {
    if (!stream) { errno = EBADF; return NULL; }
    /* Close old fd */
    simpleos_syscall(33, stream->fd, 0, 0, 0, 0);

    /* Parse mode flags (reuse fopen logic) */
    int flags = 0;
    if (strcmp(mode, "r") == 0 || strcmp(mode, "rb") == 0)
        flags = O_RDONLY;
    else if (strcmp(mode, "w") == 0 || strcmp(mode, "wb") == 0)
        flags = O_WRONLY | O_CREAT | O_TRUNC;
    else if (strcmp(mode, "a") == 0 || strcmp(mode, "ab") == 0)
        flags = O_WRONLY | O_CREAT | O_APPEND;
    else if (strcmp(mode, "r+") == 0 || strcmp(mode, "rb+") == 0 ||
             strcmp(mode, "r+b") == 0)
        flags = O_RDWR;
    else if (strcmp(mode, "w+") == 0 || strcmp(mode, "wb+") == 0 ||
             strcmp(mode, "w+b") == 0)
        flags = O_RDWR | O_CREAT | O_TRUNC;
    else if (strcmp(mode, "a+") == 0 || strcmp(mode, "ab+") == 0 ||
             strcmp(mode, "a+b") == 0)
        flags = O_RDWR | O_CREAT | O_APPEND;
    else {
        errno = EINVAL;
        return NULL;
    }

    int fd = (int)simpleos_syscall(30, (int64_t)path, (int64_t)strlen(path),
                                    flags, 0644, 0);
    if (fd < 0) { errno = (int)(-fd); return NULL; }

    stream->fd    = fd;
    stream->eof   = 0;
    stream->error = 0;
    stream->mode  = flags;
    return stream;
}
