/*
 * Fork-without-exec support for test runner isolation.
 *
 * Provides fork() + pipe capture for running test files in child processes
 * without the overhead of exec(). The child inherits the loaded binary
 * (COW pages) and can call core_interpret() directly.
 *
 * FFI-friendly API (all functions return simple types):
 *   rt_fork_child_setup()        - fork + redirect child stdio to pipes
 *   rt_fork_parent_wait()        - read pipes, waitpid, store results
 *   rt_fork_parent_stdout()      - get captured stdout after wait
 *   rt_fork_parent_stderr()      - get captured stderr after wait
 *   rt_fork_child_exit()         - _exit() without atexit handlers
 */

#ifndef SPL_RUNTIME_FORK_H
#define SPL_RUNTIME_FORK_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Fork the current process and set up stdout/stderr pipe capture.
 *
 * In the child: stdout (fd 1) and stderr (fd 2) are redirected to pipes.
 * In the parent: pipe read ends are stored internally for rt_fork_parent_wait().
 *
 * Returns:
 *   0    = child process (stdio redirected to pipes)
 *   > 0  = parent process (value is child PID)
 *   -1   = error (fork or pipe failed)
 */
int64_t rt_fork_child_setup(void);

/*
 * Parent: read captured stdout/stderr from child, wait for exit with timeout.
 *
 * Uses poll() to multiplex reads from both pipes to avoid deadlock.
 * If child exceeds timeout_ms, sends SIGKILL and reaps.
 * Results are stored internally — retrieve with rt_fork_parent_stdout/stderr.
 *
 * Parameters:
 *   child_pid   - PID returned by rt_fork_child_setup()
 *   timeout_ms  - wall-clock timeout in milliseconds (0 = no timeout)
 *
 * Returns:
 *   exit code of child process
 *   -1 on timeout or signal death
 */
int64_t rt_fork_parent_wait(int64_t child_pid, int64_t timeout_ms);

/*
 * Get captured stdout from the last rt_fork_parent_wait() call.
 * Returns empty string if no data or if called before wait.
 * The returned string is valid until the next rt_fork_parent_wait() call.
 */
const char* rt_fork_parent_stdout(void);

/*
 * Get captured stderr from the last rt_fork_parent_wait() call.
 * Returns empty string if no data or if called before wait.
 * The returned string is valid until the next rt_fork_parent_wait() call.
 */
const char* rt_fork_parent_stderr(void);

/*
 * Child: exit immediately without atexit handlers or stdio flush.
 * Uses _exit() to avoid double-flushing stdio buffers inherited from parent.
 */
void rt_fork_child_exit(int64_t exit_code);

#ifdef __cplusplus
}
#endif

#endif /* SPL_RUNTIME_FORK_H */
