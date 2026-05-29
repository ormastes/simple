/*
 * PTY (Pseudo-Terminal) runtime support.
 *
 * Provides:
 *   rt_pty_open(rows, cols) -> i32   — opens a PTY master/slave pair, returns master fd
 *   rt_pty_spawn(master_fd, shell)   — forks a shell on the slave side, returns child PID
 *
 * Design:
 *   - rt_pty_open: uses openpty() to allocate a PTY pair with the requested window size.
 *     Returns the master fd; the slave fd is stored internally per-master in a small table.
 *   - rt_pty_spawn: looks up the slave fd for master_fd, then forks.  The child redirects
 *     stdin/stdout/stderr to the slave fd (setsid + ioctl TIOCSCTTY) and execs the shell.
 *     The parent closes the slave fd (no longer needed on the master side) and returns the PID.
 *   - Windows: stubs return -1 / error.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I src/runtime src/runtime/runtime_pty.c
 */

#ifdef _WIN32

#include <stdint.h>

int32_t rt_pty_open(int32_t rows, int32_t cols) {
    (void)rows; (void)cols;
    return -1;
}

int64_t rt_pty_spawn(int32_t master_fd, const char *shell) {
    (void)master_fd; (void)shell;
    return -1;
}

#else /* POSIX */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <errno.h>
#include <sys/ioctl.h>
#include <termios.h>

/* Header for openpty / forkpty varies by platform */
#if defined(__linux__)
#  include <pty.h>
#elif defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__NetBSD__)
#  include <util.h>
#else
#  include <pty.h>   /* best-effort fallback */
#endif

/* ------------------------------------------------------------------ */
/* Slave-fd table — maps master fd -> slave fd so rt_pty_spawn can     */
/* set up the child's controlling terminal.                            */
/* ------------------------------------------------------------------ */

#define RT_PTY_MAX 16

/* NOTE: this table is not thread-safe — same pattern as runtime_fork.c and
 * runtime_process.c (all single-threaded call paths in the current runtime). */
static struct {
    int master_fd;
    int slave_fd;
} s_pty_table[RT_PTY_MAX];
static int s_pty_count = 0;

static void pty_table_insert(int master_fd, int slave_fd) {
    if (s_pty_count < RT_PTY_MAX) {
        s_pty_table[s_pty_count].master_fd = master_fd;
        s_pty_table[s_pty_count].slave_fd  = slave_fd;
        s_pty_count++;
    }
}

static int pty_table_find_slave(int master_fd) {
    for (int i = 0; i < s_pty_count; i++) {
        if (s_pty_table[i].master_fd == master_fd) {
            return s_pty_table[i].slave_fd;
        }
    }
    return -1;
}

static void pty_table_remove(int master_fd) {
    for (int i = 0; i < s_pty_count; i++) {
        if (s_pty_table[i].master_fd == master_fd) {
            s_pty_table[i] = s_pty_table[--s_pty_count];
            return;
        }
    }
}

/* ------------------------------------------------------------------ */
/* rt_pty_open                                                         */
/* ------------------------------------------------------------------ */

/*
 * Open a PTY pair with the given terminal dimensions.
 *
 * Parameters:
 *   rows — terminal height in character rows
 *   cols — terminal width  in character columns
 *
 * Returns:
 *   master fd (>= 0) on success
 *   -1 on error
 */
int32_t rt_pty_open(int32_t rows, int32_t cols) {
    int master_fd = -1;
    int slave_fd  = -1;

    struct winsize ws;
    memset(&ws, 0, sizeof(ws));
    ws.ws_row = (unsigned short)(rows > 0 ? rows : 24);
    ws.ws_col = (unsigned short)(cols > 0 ? cols : 80);

    if (openpty(&master_fd, &slave_fd, NULL, NULL, &ws) < 0) {
        return -1;
    }

    /* Set master fd non-blocking so callers can poll without blocking */
    int flags = fcntl(master_fd, F_GETFL, 0);
    if (flags >= 0) {
        fcntl(master_fd, F_SETFL, flags | O_NONBLOCK);
    }

    pty_table_insert(master_fd, slave_fd);
    return (int32_t)master_fd;
}

/* ------------------------------------------------------------------ */
/* rt_pty_spawn                                                        */
/* ------------------------------------------------------------------ */

/*
 * Fork a shell process attached to the slave end of the PTY.
 *
 * The child:
 *   1. Starts a new session (setsid).
 *   2. Makes the slave fd the controlling terminal (TIOCSCTTY).
 *   3. Redirects stdin/stdout/stderr to the slave fd.
 *   4. exec's the shell (bare path, no extra arguments).
 *
 * The parent:
 *   - Closes the slave fd (the child holds it now).
 *   - Removes the entry from the slave table.
 *   - Returns the child PID.
 *
 * Parameters:
 *   master_fd  — fd returned by rt_pty_open
 *   shell      — absolute or relative path to the shell binary (e.g. "/bin/sh")
 *
 * Returns:
 *   child PID (> 0) on success
 *   -1 on error
 */
int64_t rt_pty_spawn(int32_t master_fd, const char *shell) {
    if (!shell || shell[0] == '\0') {
        return -1;
    }

    int slave_fd = pty_table_find_slave((int)master_fd);
    if (slave_fd < 0) {
        return -1;
    }

    /* Flush stdio before fork to avoid double output */
    fflush(stdout);
    fflush(stderr);

    pid_t pid = fork();
    if (pid < 0) {
        return -1;
    }

    if (pid == 0) {
        /* ===== CHILD ===== */

        /* Become a new session leader so we can acquire a controlling terminal */
        if (setsid() < 0) {
            _exit(1);
        }

        /* Acquire slave as controlling terminal */
#ifdef TIOCSCTTY
        if (ioctl(slave_fd, TIOCSCTTY, 0) < 0) {
            _exit(1);
        }
#endif

        /* Wire stdin/stdout/stderr to the slave pty */
        dup2(slave_fd, STDIN_FILENO);
        dup2(slave_fd, STDOUT_FILENO);
        dup2(slave_fd, STDERR_FILENO);

        /* Close extra fds — master and original slave */
        if (slave_fd > STDERR_FILENO) {
            close(slave_fd);
        }
        close((int)master_fd);

        /* Reset signal handlers inherited from parent */
        signal(SIGINT,  SIG_DFL);
        signal(SIGTERM, SIG_DFL);
        signal(SIGPIPE, SIG_DFL);
        signal(SIGHUP,  SIG_DFL);

        /* exec the shell — argv[0] = basename of shell path */
        const char *argv0 = strrchr(shell, '/');
        argv0 = argv0 ? argv0 + 1 : shell;
        execlp(shell, argv0, (char *)NULL);

        /* exec failed */
        _exit(127);
    }

    /* ===== PARENT ===== */

    /* Close slave — child owns it now */
    close(slave_fd);
    pty_table_remove((int)master_fd);

    return (int64_t)pid;
}

#endif /* _WIN32 / POSIX */
