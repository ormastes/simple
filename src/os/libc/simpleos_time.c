/*
 * SimpleOS Libc Shim -- Time functions
 *
 * Provides clock_gettime, gettimeofday, time, nanosleep, gmtime, localtime,
 * mktime, difftime, strftime, clock.
 *
 * Syscall 50 = ClockGetTime: clk_id, buf_ptr -> [seconds, nanoseconds]
 * Syscall 51 = Nanosleep: nanoseconds
 */

#include "include/time.h"
#include "include/sys/types.h"
#include "include/string.h"
#include "include/stdio.h"

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);
extern int errno;

/* ====================================================================
 * 1. Clock / time syscalls
 * ==================================================================== */

int clock_gettime(clockid_t clk_id, struct timespec *tp) {
    int64_t buf[2]; /* [seconds, nanoseconds] */
    int64_t r = simpleos_syscall(50, (int64_t)clk_id, (int64_t)(uintptr_t)buf,
                                  0, 0, 0);
    if (r < 0) {
        errno = (int)(-r);
        return -1;
    }
    tp->tv_sec  = (time_t)buf[0];
    tp->tv_nsec = (long)buf[1];
    return 0;
}

int gettimeofday(struct timeval *tv, void *tz) {
    (void)tz;
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts) < 0) return -1;
    tv->tv_sec  = ts.tv_sec;
    tv->tv_usec = ts.tv_nsec / 1000;
    return 0;
}

time_t time(time_t *tloc) {
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts) < 0) return (time_t)-1;
    if (tloc) *tloc = ts.tv_sec;
    return ts.tv_sec;
}

clock_t clock(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) < 0) return (clock_t)-1;
    return (clock_t)(ts.tv_sec * CLOCKS_PER_SEC + ts.tv_nsec / 1000);
}

int nanosleep(const struct timespec *req, struct timespec *rem) {
    int64_t nanos = (int64_t)req->tv_sec * 1000000000LL + (int64_t)req->tv_nsec;
    simpleos_syscall(51, nanos, 0, 0, 0, 0);
    if (rem) {
        rem->tv_sec  = 0;
        rem->tv_nsec = 0;
    }
    return 0;
}

double difftime(time_t t1, time_t t0) {
    return (double)(t1 - t0);
}

/* ====================================================================
 * 2. Calendar time -- gmtime / localtime / mktime
 * ==================================================================== */

static struct tm _tm_buf;
static int _days_in_month[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};

static int _is_leap(int year) {
    return (year % 4 == 0 && (year % 100 != 0 || year % 400 == 0));
}

struct tm *gmtime(const time_t *timer) {
    time_t t = *timer;

    /* Seconds within the day */
    _tm_buf.tm_sec  = (int)(t % 60); t /= 60;
    _tm_buf.tm_min  = (int)(t % 60); t /= 60;
    _tm_buf.tm_hour = (int)(t % 24); t /= 24;

    /* Days since epoch (Jan 1, 1970 was a Thursday = 4) */
    int days = (int)t;
    _tm_buf.tm_wday = (days + 4) % 7;

    int year = 1970;
    while (1) {
        int ydays = _is_leap(year) ? 366 : 365;
        if (days < ydays) break;
        days -= ydays;
        year++;
    }
    _tm_buf.tm_year = year - 1900;
    _tm_buf.tm_yday = days;

    int leap = _is_leap(year);
    _days_in_month[1] = leap ? 29 : 28;

    int month = 0;
    while (month < 12 && days >= _days_in_month[month]) {
        days -= _days_in_month[month];
        month++;
    }
    _tm_buf.tm_mon  = month;
    _tm_buf.tm_mday = days + 1;
    _tm_buf.tm_isdst = 0;

    return &_tm_buf;
}

struct tm *localtime(const time_t *timer) {
    /* No timezone support -- localtime == gmtime */
    return gmtime(timer);
}

time_t mktime(struct tm *tm) {
    time_t result = 0;
    int target_year = tm->tm_year + 1900;

    for (int y = 1970; y < target_year; y++) {
        result += _is_leap(y) ? 366 * 86400 : 365 * 86400;
    }

    int leap = _is_leap(target_year);
    _days_in_month[1] = leap ? 29 : 28;

    for (int m = 0; m < tm->tm_mon; m++) {
        result += _days_in_month[m] * 86400;
    }

    result += (time_t)(tm->tm_mday - 1) * 86400;
    result += (time_t)tm->tm_hour * 3600;
    result += (time_t)tm->tm_min * 60;
    result += (time_t)tm->tm_sec;

    return result;
}

/* ====================================================================
 * 3. strftime -- minimal format specifiers
 *
 * Supported: %Y %m %d %H %M %S %j %w %% %n %t
 * ==================================================================== */

/* Write a zero-padded decimal of `digits` width into buf */
static size_t _fmt_dec(char *buf, size_t max, size_t pos, int val, int digits) {
    char tmp[8];
    int len = 0;
    int v = val < 0 ? -val : val;
    do {
        tmp[len++] = '0' + (char)(v % 10);
        v /= 10;
    } while (v > 0);
    while (len < digits) tmp[len++] = '0';
    for (int i = len - 1; i >= 0; i--) {
        if (pos < max) buf[pos] = tmp[i];
        pos++;
    }
    return pos;
}

size_t strftime(char *s, size_t max, const char *fmt, const struct tm *tm) {
    size_t pos = 0;

    while (*fmt && pos < max) {
        if (*fmt != '%') {
            s[pos++] = *fmt++;
            continue;
        }
        fmt++; /* skip '%' */
        switch (*fmt) {
        case 'Y':  /* 4-digit year */
            pos = _fmt_dec(s, max, pos, tm->tm_year + 1900, 4);
            break;
        case 'm':  /* month 01-12 */
            pos = _fmt_dec(s, max, pos, tm->tm_mon + 1, 2);
            break;
        case 'd':  /* day 01-31 */
            pos = _fmt_dec(s, max, pos, tm->tm_mday, 2);
            break;
        case 'H':  /* hour 00-23 */
            pos = _fmt_dec(s, max, pos, tm->tm_hour, 2);
            break;
        case 'M':  /* minute 00-59 */
            pos = _fmt_dec(s, max, pos, tm->tm_min, 2);
            break;
        case 'S':  /* second 00-60 */
            pos = _fmt_dec(s, max, pos, tm->tm_sec, 2);
            break;
        case 'j':  /* day of year 001-366 */
            pos = _fmt_dec(s, max, pos, tm->tm_yday + 1, 3);
            break;
        case 'w':  /* weekday 0-6 */
            pos = _fmt_dec(s, max, pos, tm->tm_wday, 1);
            break;
        case 'n':  /* newline */
            if (pos < max) s[pos] = '\n';
            pos++;
            break;
        case 't':  /* tab */
            if (pos < max) s[pos] = '\t';
            pos++;
            break;
        case '%':
            if (pos < max) s[pos] = '%';
            pos++;
            break;
        default:
            /* Unknown specifier -- output literally */
            if (pos < max) s[pos] = '%';
            pos++;
            if (pos < max) s[pos] = *fmt;
            pos++;
            break;
        }
        if (*fmt) fmt++;
    }

    /* Null-terminate */
    if (pos < max)
        s[pos] = '\0';
    else if (max > 0)
        s[max - 1] = '\0';

    return pos;
}
