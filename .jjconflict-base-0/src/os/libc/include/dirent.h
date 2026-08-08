/*
 * SimpleOS <dirent.h> — directory entry definitions
 */

#ifndef _SIMPLEOS_DIRENT_H
#define _SIMPLEOS_DIRENT_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

/* Directory entry types */
#define DT_UNKNOWN 0
#define DT_FIFO    1
#define DT_CHR     2
#define DT_DIR     4
#define DT_BLK     6
#define DT_REG     8
#define DT_LNK    10

struct dirent {
    ino_t  d_ino;
    unsigned char d_type;
    char   d_name[256];
};

/* Opaque directory stream */
typedef struct __simpleos_DIR DIR;

DIR           *opendir(const char *name);
struct dirent *readdir(DIR *dirp);
int            closedir(DIR *dirp);
void           rewinddir(DIR *dirp);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_DIRENT_H */
