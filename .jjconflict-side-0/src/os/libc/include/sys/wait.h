/*
 * SimpleOS <sys/wait.h> — child process status helpers
 */

#ifndef _SIMPLEOS_SYS_WAIT_H
#define _SIMPLEOS_SYS_WAIT_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

#define WNOHANG    1
#define WUNTRACED  2
#define WCONTINUED 8

#define WEXITSTATUS(status) (((status) >> 8) & 0xff)
#define WTERMSIG(status)    ((status) & 0x7f)
#define WSTOPSIG(status)    WEXITSTATUS(status)
#define WIFEXITED(status)   (WTERMSIG(status) == 0)
#define WIFSIGNALED(status) (WTERMSIG(status) != 0 && WTERMSIG(status) != 0x7f)
#define WIFSTOPPED(status)  (((status) & 0xff) == 0x7f)
#define WIFCONTINUED(status) ((status) == 0xffff)

pid_t wait(int *wstatus);
pid_t waitpid(pid_t pid, int *wstatus, int options);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_SYS_WAIT_H */
