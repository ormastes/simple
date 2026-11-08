/* Unix submission admission only. Never used as a workload lifetime timer.
 * A numeric deadline is data supplied after the caller verifies authority. */
#ifndef SIMPLE_PROCESS_SUBMISSION_ADMISSION_V5_H
#define SIMPLE_PROCESS_SUBMISSION_ADMISSION_V5_H
#include <stdint.h>
#include <limits.h>
#include <errno.h>
#include <time.h>
/* Test translation units may substitute only the clock syscall. Production
 * has no environment switch, exported clock setter or fabricated success. */
#ifndef POV5_ADMISSION_CLOCK_GETTIME
#define POV5_ADMISSION_CLOCK_GETTIME clock_gettime
#endif
static int pov5_submission_admission_check(int64_t expires_at_unix_ms) {
    if (expires_at_unix_ms==0) return 0; /* Existing V4 compatibility route. */
    if (expires_at_unix_ms<0) return EINVAL;
    struct timespec now;
    if (POV5_ADMISSION_CLOCK_GETTIME(CLOCK_REALTIME,&now)!=0 ||
        now.tv_sec<0 || now.tv_nsec<0 || now.tv_nsec>=1000000000L ||
        (uint64_t)now.tv_sec>(uint64_t)INT64_MAX/1000) return EIO;
    int64_t seconds=(int64_t)now.tv_sec*1000;
    int64_t fraction=now.tv_nsec/1000000;
    if (seconds>INT64_MAX-fraction || seconds+fraction<=0) return EIO;
    return seconds+fraction>=expires_at_unix_ms?ETIMEDOUT:0;
}
#endif
