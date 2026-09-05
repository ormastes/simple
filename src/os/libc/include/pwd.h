#ifndef SIMPLEOS_PWD_H
#define SIMPLEOS_PWD_H

#include <sys/types.h>

struct passwd {
    char *pw_name;
    char *pw_passwd;
    uid_t pw_uid;
    gid_t pw_gid;
    char *pw_gecos;
    char *pw_dir;
    char *pw_shell;
};

#ifdef __cplusplus
extern "C" {
#endif

int getpwuid_r(uid_t uid, struct passwd *pwd, char *buf, unsigned long buflen,
               struct passwd **result);
int getpwnam_r(const char *name, struct passwd *pwd, char *buf,
               unsigned long buflen, struct passwd **result);
struct passwd *getpwuid(uid_t uid);
struct passwd *getpwnam(const char *name);

#ifdef __cplusplus
}
#endif

#endif
