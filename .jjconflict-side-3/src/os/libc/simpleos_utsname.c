#include "include/sys/utsname.h"
#include "include/errno.h"
#include "include/string.h"

int uname(struct utsname *buf) {
    if (!buf) {
        errno = EINVAL;
        return -1;
    }

    memset(buf, 0, sizeof(*buf));
    strncpy(buf->sysname, "SimpleOS", _UTSNAME_LENGTH - 1);
    strncpy(buf->nodename, "simpleos", _UTSNAME_LENGTH - 1);
    strncpy(buf->release, "0.0", _UTSNAME_LENGTH - 1);
    strncpy(buf->version, "0", _UTSNAME_LENGTH - 1);
    strncpy(buf->machine, "unknown", _UTSNAME_LENGTH - 1);
    return 0;
}
