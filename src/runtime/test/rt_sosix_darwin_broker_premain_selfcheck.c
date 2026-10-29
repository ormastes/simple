/* Linked into a test copy of the canonical helper, before its main function. */
#include <crt_externs.h>
#include <libproc.h>
#include <sys/proc_info.h>
#include <unistd.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
__attribute__((constructor)) static void verify_premain(void) {
    if (**_NSGetEnviron()) _exit(81);
    struct proc_fdinfo fds[16];
    int count = proc_pidinfo(getpid(), PROC_PIDLISTFDS, 0, fds, sizeof(fds));
    if (count < 0 || count >= (int)sizeof(fds) || count % sizeof(fds[0])) _exit(82);
    for (int i = 0; i < count / (int)sizeof(fds[0]); ++i)
        if (fds[i].proc_fd > 2) _exit(83);
    int argc = *_NSGetArgc(); char **argv = *_NSGetArgv();
    if (argc == 5) {
        char path[PATH_MAX]; snprintf(path, sizeof(path), "%s.entered", argv[2]);
        int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
        if (fd < 0) _exit(84);
        (void)write(fd, "entered", 7); close(fd);
    }
}
