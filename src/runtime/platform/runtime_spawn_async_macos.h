/* Darwin async children inherit only open, non-CLOEXEC standard streams.
 * Keep parent file/pipe/socket ownership out of independently running workers.
 * Both runtime lanes use this helper; no child-side allocation after fork. */
#ifndef SIMPLE_RUNTIME_SPAWN_ASYNC_MACOS_H
#define SIMPLE_RUNTIME_SPAWN_ASYNC_MACOS_H
#if defined(__APPLE__)
static int runtime_spawn_async_macos(pid_t* pid, const char* cmd, char** argv) {
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attributes;
    int error = posix_spawn_file_actions_init(&actions);
    if (error != 0) return error;
    error = posix_spawnattr_init(&attributes);
    if (error != 0) {
        (void)posix_spawn_file_actions_destroy(&actions);
        return error;
    }
    error = posix_spawnattr_setflags(&attributes, POSIX_SPAWN_CLOEXEC_DEFAULT);
    for (int fd = STDIN_FILENO; error == 0 && fd <= STDERR_FILENO; fd++) {
        int flags = fcntl(fd, F_GETFD);
        if (flags >= 0 && (flags & FD_CLOEXEC) == 0)
            error = posix_spawn_file_actions_addinherit_np(&actions, fd);
        else if (flags < 0 && errno != EBADF)
            error = errno;
    }
    if (error == 0)
        error = posix_spawnp(pid, cmd, &actions, &attributes, argv, *_NSGetEnviron());
    (void)posix_spawnattr_destroy(&attributes);
    (void)posix_spawn_file_actions_destroy(&actions);
    return error;
}
#endif
#endif
