#ifndef SHIM_UNISTD_H
#define SHIM_UNISTD_H
#include <stddef.h>
#include <sys/stat.h>
typedef long ssize_t;
#define SEEK_SET 0
ssize_t read(int, void *, size_t);
int close(int);
off_t lseek(int, off_t, int);
int execve(const char *, char *const[], char *const[]);
#ifndef __APPLE__
int fexecve(int, char *const[], char *const[]);
#endif
#endif
