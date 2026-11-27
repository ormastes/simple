/* Focused Unix clock mechanism tests. NOT_RUN in this source-only task.
 * The macro substitutes only a test-TU clock syscall; production has no setter.
 * This does not claim live child/retirement or Simple ABI qualification. */
#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <time.h>
static int clock_mode;
static int clock_calls;
static int admission_test_clock(clockid_t clock,struct timespec* value) {
    clock_calls++;
    assert(clock==CLOCK_REALTIME);
    if (clock_mode==1) {errno=EIO;return -1;}
    if (clock_mode==2) {value->tv_sec=0;value->tv_nsec=0;return 0;}
    if (clock_mode==3) {value->tv_sec=5;value->tv_nsec=1000000000L;return 0;}
    value->tv_sec=100;value->tv_nsec=123000000L;return 0;
}
#define POV5_ADMISSION_CLOCK_GETTIME admission_test_clock
#include "../runtime_process_submission_admission_v5.h"
int main(void) {
    assert(pov5_submission_admission_check(0)==0 && clock_calls==0);
    assert(pov5_submission_admission_check(-1)==EINVAL && clock_calls==0);
    assert(pov5_submission_admission_check(100124)==0);
    assert(pov5_submission_admission_check(100123)==ETIMEDOUT);
    assert(pov5_submission_admission_check(100122)==ETIMEDOUT);
    clock_mode=1;assert(pov5_submission_admission_check(100124)==EIO);
    clock_mode=2;assert(pov5_submission_admission_check(100124)==EIO);
    clock_mode=3;assert(pov5_submission_admission_check(100124)==EIO);
    return 0;
}
