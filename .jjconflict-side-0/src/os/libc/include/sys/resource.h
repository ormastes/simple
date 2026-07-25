#ifndef SIMPLEOS_SYS_RESOURCE_H
#define SIMPLEOS_SYS_RESOURCE_H

#include <sys/types.h>
#include <sys/time.h>

#define RUSAGE_SELF 0
#define RUSAGE_CHILDREN -1

#define RLIMIT_DATA 2
#define RLIMIT_STACK 3
#define RLIMIT_CORE 4

typedef unsigned long rlim_t;
#define RLIM_INFINITY ((rlim_t)-1)

struct rusage {
    struct timeval ru_utime;
    struct timeval ru_stime;
    long ru_maxrss;
};

struct rlimit {
    rlim_t rlim_cur;
    rlim_t rlim_max;
};

#ifdef __cplusplus
extern "C" {
#endif

int getrusage(int who, struct rusage *usage);
int getrlimit(int resource, struct rlimit *rlim);
int setrlimit(int resource, const struct rlimit *rlim);

#ifdef __cplusplus
}
#endif

#endif
