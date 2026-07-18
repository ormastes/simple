#include <errno.h>
#include <stddef.h>
#include "include/pwd.h"

#ifndef ENOSYS
#define ENOSYS 38
#endif

int getpwuid_r(uid_t uid, struct passwd *pwd, char *buf, unsigned long buflen,
               struct passwd **result) {
    (void)uid; (void)pwd; (void)buf; (void)buflen;
    if (result) *result = 0;
    return ENOSYS;  /* getpwuid_r returns errno on failure, 0 on success */
}

int getpwnam_r(const char *name, struct passwd *pwd, char *buf, unsigned long buflen,
               struct passwd **result) {
    (void)name; (void)pwd; (void)buf; (void)buflen;
    if (result) *result = 0;
    return ENOSYS;
}

struct passwd *getpwuid(uid_t uid) { (void)uid; errno = ENOSYS; return 0; }
struct passwd *getpwnam(const char *name) { (void)name; errno = ENOSYS; return 0; }
