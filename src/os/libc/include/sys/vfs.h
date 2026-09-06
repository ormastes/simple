#ifndef SIMPLEOS_SYS_VFS_H
#define SIMPLEOS_SYS_VFS_H

#include <sys/statvfs.h>

#define statfs statvfs
#define fstatfs fstatvfs

#endif
