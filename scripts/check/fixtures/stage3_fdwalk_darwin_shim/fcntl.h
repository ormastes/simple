#ifndef SHIM_FCNTL_H
#define SHIM_FCNTL_H
#define O_RDONLY 0
#define O_NOFOLLOW 0x100
#define O_CLOEXEC 0x1000000
#define O_DIRECTORY 0x100000
#define F_DUPFD_CLOEXEC 67
#define F_SETFD 2
#define FD_CLOEXEC 1
#ifdef __APPLE__
#define F_GETPATH 50
#endif
int openat(int, const char *, int, ...);
int fcntl(int, int, ...);
#endif
