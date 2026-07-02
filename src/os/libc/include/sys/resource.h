#ifndef SIMPLEOS_SYS_RESOURCE_H
#define SIMPLEOS_SYS_RESOURCE_H

#include <sys/types.h>
#include <sys/time.h>

#define RUSAGE_SELF 0
#define RUSAGE_CHILDREN -1

struct rusage {
    struct timeval ru_utime;
    struct timeval ru_stime;
    long ru_maxrss;
};

#ifdef __cplusplus
extern "C" {
#endif

int getrusage(int who, struct rusage *usage);

#ifdef __cplusplus
}
#endif

#endif
