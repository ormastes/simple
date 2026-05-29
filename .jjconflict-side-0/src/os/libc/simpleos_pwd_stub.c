#include <errno.h>
#include <stddef.h>

#ifndef ENOSYS
#define ENOSYS 38
#endif

/* Inline forward declarations — SimpleOS has no getpwent db. */
struct passwd {
    char *pw_name;
    char *pw_passwd;
    unsigned pw_uid;
    unsigned pw_gid;
    char *pw_gecos;
    char *pw_dir;
    char *pw_shell;
};

int getpwuid_r(unsigned uid, struct passwd *pwd, char *buf, unsigned long buflen,
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

struct passwd *getpwuid(unsigned uid) { (void)uid; errno = ENOSYS; return 0; }
struct passwd *getpwnam(const char *name) { (void)name; errno = ENOSYS; return 0; }
