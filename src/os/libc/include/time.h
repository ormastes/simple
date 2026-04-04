/*
 * SimpleOS <time.h> — time types and functions
 */

#ifndef _SIMPLEOS_TIME_H
#define _SIMPLEOS_TIME_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

#ifndef NULL
#define NULL ((void *)0)
#endif

#define CLOCKS_PER_SEC 1000000

#define CLOCK_REALTIME  0
#define CLOCK_MONOTONIC 1

typedef long clock_t;

struct timespec {
    time_t tv_sec;
    long   tv_nsec;
};

struct timeval {
    time_t      tv_sec;
    suseconds_t tv_usec;
};

struct tm {
    int tm_sec;    /* seconds [0, 60] */
    int tm_min;    /* minutes [0, 59] */
    int tm_hour;   /* hours [0, 23] */
    int tm_mday;   /* day of month [1, 31] */
    int tm_mon;    /* month [0, 11] */
    int tm_year;   /* years since 1900 */
    int tm_wday;   /* day of week [0, 6] (Sunday = 0) */
    int tm_yday;   /* day of year [0, 365] */
    int tm_isdst;  /* daylight saving time flag */
};

time_t time(time_t *tloc);
time_t mktime(struct tm *tm);
double difftime(time_t time1, time_t time0);

struct tm *localtime(const time_t *timep);
struct tm *gmtime(const time_t *timep);

size_t strftime(char *s, size_t max, const char *format, const struct tm *tm);

int clock_gettime(clockid_t clk_id, struct timespec *tp);
int gettimeofday(struct timeval *tv, void *tz);
int nanosleep(const struct timespec *req, struct timespec *rem);

clock_t clock(void);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_TIME_H */
