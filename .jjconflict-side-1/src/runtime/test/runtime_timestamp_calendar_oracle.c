/* Test-only C calendar oracle retained for Pure Simple differential vectors. */
#include <stdint.h>

static void oracle_days_to_ymd(int64_t z, int32_t *year, int32_t *month, int32_t *day) {
    z += 719468;
    int64_t era = (z >= 0 ? z : z - 146096) / 146097;
    int64_t doe = z - era * 146097;
    int64_t yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    int64_t y = yoe + era * 400;
    int64_t doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    int64_t mp = (5 * doy + 2) / 153;
    int64_t d = doy - (153 * mp + 2) / 5 + 1;
    int64_t m = mp < 10 ? mp + 3 : mp - 9;
    y += (m <= 2);
    *year = (int32_t)y;
    *month = (int32_t)m;
    *day = (int32_t)d;
}

static int64_t oracle_micros_to_days(int64_t micros) {
    int64_t days = micros / 86400000000LL;
    if (micros < 0 && micros % 86400000000LL != 0) days--;
    return days;
}

static int64_t oracle_time_of_day_micros(int64_t micros) {
    int64_t value = micros % 86400000000LL;
    return value < 0 ? value + 86400000000LL : value;
}

int32_t rt_timestamp_oracle_get_year(int64_t micros) {
    int32_t y, m, d;
    oracle_days_to_ymd(oracle_micros_to_days(micros), &y, &m, &d);
    return y;
}
int32_t rt_timestamp_oracle_get_month(int64_t micros) {
    int32_t y, m, d;
    oracle_days_to_ymd(oracle_micros_to_days(micros), &y, &m, &d);
    return m;
}
int32_t rt_timestamp_oracle_get_day(int64_t micros) {
    int32_t y, m, d;
    oracle_days_to_ymd(oracle_micros_to_days(micros), &y, &m, &d);
    return d;
}
int32_t rt_timestamp_oracle_get_hour(int64_t micros) {
    return (int32_t)(oracle_time_of_day_micros(micros) / 3600000000LL);
}
int32_t rt_timestamp_oracle_get_minute(int64_t micros) {
    return (int32_t)((oracle_time_of_day_micros(micros) / 60000000LL) % 60);
}
int32_t rt_timestamp_oracle_get_second(int64_t micros) {
    return (int32_t)((oracle_time_of_day_micros(micros) / 1000000LL) % 60);
}
int32_t rt_timestamp_oracle_get_microsecond(int64_t micros) {
    return (int32_t)(oracle_time_of_day_micros(micros) % 1000000LL);
}

int64_t rt_timestamp_oracle_from_components(int32_t year, int32_t month, int32_t day,
                                            int32_t hour, int32_t minute, int32_t second,
                                            int32_t microsecond) {
    int32_t y = year - (month <= 2 ? 1 : 0);
    int32_t m = month + (month <= 2 ? 9 : -3);
    int64_t era = (int64_t)(y >= 0 ? y : y - 399) / 400;
    int64_t yoe = (int64_t)y - era * 400;
    int64_t doy = (153 * m + 2) / 5 + day - 1;
    int64_t doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    int64_t days = era * 146097 + doe - 719468;
    int64_t secs = days * 86400LL + (int64_t)hour * 3600 +
                   (int64_t)minute * 60 + (int64_t)second;
    return secs * 1000000LL + microsecond;
}
int64_t rt_timestamp_oracle_add_days(int64_t micros, int64_t days) {
    return micros + days * 86400000000LL;
}
int64_t rt_timestamp_oracle_diff_days(int64_t micros1, int64_t micros2) {
    return (micros1 - micros2) / 86400000000LL;
}
