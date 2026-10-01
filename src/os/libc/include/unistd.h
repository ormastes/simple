/*
 * SimpleOS <unistd.h> — POSIX API definitions
 */

#ifndef _SIMPLEOS_UNISTD_H
#define _SIMPLEOS_UNISTD_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

#ifndef NULL
#define NULL ((void *)0)
#endif

/* Standard file descriptors */
#define STDIN_FILENO  0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

/* access() mode flags */
#define F_OK 0
#define R_OK 4
#define W_OK 2
#define X_OK 1

/* sysconf names */
#define _SC_PAGESIZE         30
#define _SC_NPROCESSORS_CONF 83
/* _SC_NPROCESSORS_ONLN was missing while src/runtime/runtime_pool.c:329 asks
 * for it (the thread-pool sizing query), blocking the SimpleOS runtime
 * cross-compile. 84 is the Linux value and the natural sibling of
 * _SC_NPROCESSORS_CONF 83 already above. */
#define _SC_NPROCESSORS_ONLN 84

/* File I/O */
ssize_t read(int fd, void *buf, size_t count);
ssize_t write(int fd, const void *buf, size_t count);
ssize_t pread(int fd, void *buf, size_t count, off_t offset);
ssize_t pwrite(int fd, const void *buf, size_t count, off_t offset);
int     fsync(int fd);
int     fdatasync(int fd);
int     close(int fd);
off_t   lseek(int fd, off_t offset, int whence);
int     ftruncate(int fd, off_t length);
int     dup(int oldfd);
int     dup2(int oldfd, int newfd);
int     dup3(int oldfd, int newfd, int flags);
int     pipe(int pipefd[2]);
int     pipe2(int pipefd[2], int flags);

/* File management */
int  access(const char *path, int mode);
int  unlink(const char *path);
int  rmdir(const char *path);
int  isatty(int fd);

/* Directory */
char *getcwd(char *buf, size_t size);
int   chdir(const char *path);

/* Process */
pid_t fork(void);
int   execve(const char *path, char *const argv[], char *const envp[]);
int   execv(const char *path, char *const argv[]);
int   execvp(const char *file, char *const argv[]);
pid_t getpid(void);
pid_t getppid(void);
pid_t setsid(void);
pid_t getsid(pid_t pid);
int   setpgid(pid_t pid, pid_t pgid);
int   gethostname(char *name, size_t len);
int   getpagesize(void);
unsigned int alarm(unsigned int seconds);
void  _exit(int status) __attribute__((noreturn));

/* User / group */
uid_t getuid(void);
gid_t getgid(void);
uid_t geteuid(void);
gid_t getegid(void);

/* Sleep */
unsigned int sleep(unsigned int seconds);
int          usleep(useconds_t usec);

/* System configuration */
long sysconf(int name);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_UNISTD_H */
