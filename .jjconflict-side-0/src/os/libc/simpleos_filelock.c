#include "include/sys/file.h"
#include "include/errno.h"

int flock(int fd, int operation) {
    (void)fd;
    (void)operation;
    /* Advisory locking needs kernel-visible per-file ownership. Returning
     * success without it lets callers believe they have mutual exclusion. */
    return ENOSYS;
}
