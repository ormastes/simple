#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

static int same_file(const struct stat *a, const struct stat *b) {
    return a->st_dev == b->st_dev && a->st_ino == b->st_ino &&
           a->st_size == b->st_size &&
           a->st_mtim.tv_sec == b->st_mtim.tv_sec && a->st_mtim.tv_nsec == b->st_mtim.tv_nsec &&
           a->st_ctim.tv_sec == b->st_ctim.tv_sec && a->st_ctim.tv_nsec == b->st_ctim.tv_nsec;
}

int main(int argc, char **argv) {
    if (argc < 3 || argv[1][0] != '/' || argv[2][0] != '/') return 64;
    int fd = open(argv[1], O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) return 65;
    struct stat opened, current;
    if (fstat(fd, &opened) || !S_ISREG(opened.st_mode) || !(opened.st_mode & 0111)) return 66;
#ifdef TEST_ONLY
    const char *replacement = getenv("MCI_FEXEC_TEST_REPLACEMENT");
    if (replacement && rename(replacement, argv[1])) return 67;
#endif
    pid_t child = fork();
    if (child < 0) return 68;
    if (child == 0) {
        if (fcntl(fd, F_SETFD, 0)) _exit(125);
        argv[2] = argv[2]; /* Canonical argv[0] preserves toolchain discovery. */
        fexecve(fd, &argv[2], environ);
        _exit(errno == ENOSYS ? 126 : 127);
    }
    int status;
    if (waitpid(child, &status, 0) != child) return 69;
    if (stat(argv[1], &current) || !same_file(&opened, &current)) return 70;
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    return 128 + (WIFSIGNALED(status) ? WTERMSIG(status) : 0);
}
