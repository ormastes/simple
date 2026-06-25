/*
 * SimpleOS <sys/stat.h> — file status and permission definitions
 */

#ifndef _SIMPLEOS_SYS_STAT_H
#define _SIMPLEOS_SYS_STAT_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

/* File type flags in st_mode */
#define S_IFMT   0170000  /* mask for file type */
#define S_IFREG  0100000  /* regular file */
#define S_IFDIR  0040000  /* directory */
#define S_IFLNK  0120000  /* symbolic link */
#define S_IFCHR  0020000  /* character device */
#define S_IFBLK  0060000  /* block device */
#define S_IFIFO  0010000  /* FIFO (named pipe) */

/* File type test macros */
#define S_ISREG(m)  (((m) & S_IFMT) == S_IFREG)
#define S_ISDIR(m)  (((m) & S_IFMT) == S_IFDIR)
#define S_ISLNK(m)  (((m) & S_IFMT) == S_IFLNK)
#define S_ISCHR(m)  (((m) & S_IFMT) == S_IFCHR)
#define S_ISBLK(m)  (((m) & S_IFMT) == S_IFBLK)
#define S_ISFIFO(m) (((m) & S_IFMT) == S_IFIFO)

/* Permission bits */
#define S_IRUSR  0400   /* owner read */
#define S_IWUSR  0200   /* owner write */
#define S_IXUSR  0100   /* owner execute */
#define S_IRGRP  0040   /* group read */
#define S_IWGRP  0020   /* group write */
#define S_IXGRP  0010   /* group execute */
#define S_IROTH  0004   /* others read */
#define S_IWOTH  0002   /* others write */
#define S_IXOTH  0001   /* others execute */

#define S_IRWXU  (S_IRUSR | S_IWUSR | S_IXUSR)
#define S_IRWXG  (S_IRGRP | S_IWGRP | S_IXGRP)
#define S_IRWXO  (S_IROTH | S_IWOTH | S_IXOTH)

struct stat {
    dev_t     st_dev;
    ino_t     st_ino;
    mode_t    st_mode;
    nlink_t   st_nlink;
    uid_t     st_uid;
    gid_t     st_gid;
    dev_t     st_rdev;
    off_t     st_size;
    blksize_t st_blksize;
    blkcnt_t  st_blocks;
    time_t    st_atime;
    time_t    st_mtime;
    time_t    st_ctime;
};

int stat(const char *path, struct stat *buf);
int fstat(int fd, struct stat *buf);
int lstat(const char *path, struct stat *buf);
int mkdir(const char *path, mode_t mode);
int chmod(const char *path, mode_t mode);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_SYS_STAT_H */
