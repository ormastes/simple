#ifndef SHIM_SYS_STAT_H
#define SHIM_SYS_STAT_H
typedef int dev_t;
typedef unsigned long long ino_t;
typedef unsigned short mode_t;
typedef unsigned short nlink_t;
typedef long long off_t;
struct stat { dev_t st_dev; ino_t st_ino; mode_t st_mode; nlink_t st_nlink; off_t st_size; };
#define S_IFMT 0170000
#define S_IFDIR 0040000
#define S_IFREG 0100000
#define S_IFLNK 0120000
#define S_ISDIR(m) (((m) & S_IFMT) == S_IFDIR)
#define S_ISREG(m) (((m) & S_IFMT) == S_IFREG)
#define S_ISLNK(m) (((m) & S_IFMT) == S_IFLNK)
int fstat(int, struct stat *);
int stat(const char *, struct stat *);
int lstat(const char *, struct stat *);
/* Darwin declares fstatat and the AT_* flags in <sys/stat.h> (not <fcntl.h>);
 * stage3_fdwalk.c uses the no-follow probe to classify ENOTDIR components. */
#define AT_SYMLINK_NOFOLLOW 0x20
int fstatat(int, const char *, struct stat *, int);
#endif
int fstatat(int, const char *, struct stat *, int);
