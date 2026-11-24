#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
extern int32_t rt_timestamp_get_year(int64_t);
extern int32_t rt_timestamp_get_month(int64_t);
extern int32_t rt_timestamp_get_day(int64_t);
extern int32_t rt_timestamp_get_hour(int64_t);
extern int32_t rt_timestamp_get_minute(int64_t);
extern int32_t rt_timestamp_get_second(int64_t);
extern int32_t rt_timestamp_get_microsecond(int64_t);
extern int64_t rt_timestamp_from_components(int32_t,int32_t,int32_t,int32_t,int32_t,int32_t,int32_t);
extern int64_t rt_timestamp_add_days(int64_t,int64_t);
extern int64_t rt_timestamp_diff_days(int64_t,int64_t);
extern bool rt_progress_init(void);
extern bool rt_progress_reset(void);
extern double rt_progress_get_elapsed_seconds(void);
int main(void) {
  if (rt_timestamp_get_year(0)!=1970 || rt_timestamp_get_month(0)!=1 || rt_timestamp_get_day(0)!=1) return 11;
  if (rt_timestamp_get_hour(0)!=0 || rt_timestamp_get_minute(0)!=0 || rt_timestamp_get_second(0)!=0 || rt_timestamp_get_microsecond(123456)!=123456) return 12;
  if (rt_timestamp_from_components(1970,1,1,0,0,0,0)!=0) return 13;
  if (rt_timestamp_add_days(0,1)!=86400000000LL || rt_timestamp_diff_days(86400000000LL,0)!=1) return 14;
  if (!rt_progress_init() || !rt_progress_reset() || rt_progress_get_elapsed_seconds()<0.0) return 15;
  puts("PASS: calendar/progress C ABI");
  return 0;
}
