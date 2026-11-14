/* Linux fault injection around the actual runtime enumerator; all other
 * libc/process operations are real. No signal other than signal 0 is sent.
 * Link with -Wl,--wrap=getsid -Wl,--wrap=readdir.
 */
#define _GNU_SOURCE
#include "runtime_process_tree.h"
#include <dirent.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>

static int sid_error;
static int read_error;
static int failures;
extern pid_t __real_getsid(pid_t);
extern struct dirent* __real_readdir(DIR*);
pid_t __wrap_getsid(pid_t pid) {
    if (pid != 0 && sid_error) { errno = sid_error; return -1; }
    return __real_getsid(pid);
}
struct dirent* __wrap_readdir(DIR* dir) {
    if (read_error) { errno = read_error; return NULL; }
    return __real_readdir(dir);
}
#define CHECK(c, label) do { if (!(c)) { failures++; fprintf(stderr, "FAIL %s\n", label); } } while (0)
int main(void) {
    sid_error = EACCES;
    CHECK(rt_process_kill_session(INT32_MAX, 0) == -EACCES, "inspection denial is unknown");
    sid_error = ESRCH;
    CHECK(rt_process_kill_session(INT32_MAX, 0) == 0, "vanished entries are benign");
    sid_error = 0;
    read_error = EIO;
    CHECK(rt_process_kill_session(INT32_MAX, 0) == -EIO, "directory enumeration failure is unknown");
    read_error = 0;
    CHECK(rt_process_kill_session(INT32_MAX, 0) == 0, "actual enumeration completes");
    fprintf(stderr, "enumeration injected errors: %d failures\n", failures);
    return failures != 0;
}
