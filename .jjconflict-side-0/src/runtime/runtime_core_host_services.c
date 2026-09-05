/* Narrow hosted providers required by core-c-bootstrap tool closures.
 *
 * Keep these out of runtime_native.c: that translation unit is also used by
 * freestanding lanes.  The core-C capsule opts into this file explicitly.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif
/* macOS: _POSIX_C_SOURCE alone hides the BSD extensions in <unistd.h>, so
 * sysconf's _SC_NPROCESSORS_ONLN is undeclared and this file fails to compile
 * (`use of undeclared identifier '_SC_NPROCESSORS_ONLN'` at the sysconf call
 * below) -- which blocks the whole macOS Stage-2 bootstrap. _DARWIN_C_SOURCE
 * re-exposes them without widening anything on other platforms, where the
 * guard is inert. This has now regressed out of main TWICE via merges; if it
 * disappears again, look for a merge that reverted this hunk rather than an
 * intentional removal. */
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif

#include "runtime.h"

#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#include <sys/stat.h>
#undef max
#else
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>
#endif

static char* core_host_strdup(const char* value) {
    size_t length = strlen(value);
    char* result = (char*)malloc(length + 1);
    if (!result) return NULL;
    memcpy(result, value, length + 1);
    return result;
}

char* rt_hostname(void) {
#if defined(_WIN32)
    char buffer[256];
    DWORD length = (DWORD)sizeof(buffer);
    if (GetComputerNameA(buffer, &length)) {
        char* result = (char*)malloc((size_t)length + 1);
        if (!result) return NULL;
        memcpy(result, buffer, (size_t)length);
        result[length] = '\0';
        return result;
    }
#else
    char buffer[256];
    if (gethostname(buffer, sizeof(buffer)) == 0) {
        buffer[sizeof(buffer) - 1] = '\0';
        return core_host_strdup(buffer);
    }
#endif
    return core_host_strdup("localhost");
}

int64_t rt_unix_socket_connect(const char* path) {
#if defined(_WIN32)
    (void)path;
    return -1;
#else
    if (!path) return -1;
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    struct sockaddr_un address;
    memset(&address, 0, sizeof(address));
    address.sun_family = AF_UNIX;
    if (strlen(path) >= sizeof(address.sun_path)) {
        close(fd);
        return -1;
    }
    memcpy(address.sun_path, path, strlen(path) + 1);
    if (connect(fd, (struct sockaddr*)&address, sizeof(address)) != 0) {
        close(fd);
        return -1;
    }
    return (int64_t)fd;
#endif
}

int64_t rt_metal_is_available(void) {
    /* The portable core capsule has no Objective-C Metal provider. */
    return 0;
}

bool rt_is_debug_mode_enabled(void) {
    return false;
}

int64_t rt_file_stat(const uint8_t* path, uint64_t path_len) {
    if (!path || path_len == 0 || path_len >= 4096) return 0;
    char buffer[4096];
    memcpy(buffer, path, (size_t)path_len);
    buffer[path_len] = '\0';
    struct stat metadata;
    return stat(buffer, &metadata) == 0 ? (int64_t)metadata.st_mtime : 0;
}

bool rt_process_exists(int64_t pid) {
    if (pid <= 0) return false;
#if defined(_WIN32)
    HANDLE process = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, (DWORD)pid);
    if (!process) return GetLastError() == ERROR_ACCESS_DENIED;
    CloseHandle(process);
    return true;
#else
    return kill((pid_t)pid, 0) == 0 || errno == EPERM;
#endif
}

/* ELF spellings emitted by the self-hosted method fallback. Keep these as
 * compatibility aliases while MIR lowering converges on the libm names. */
#if !defined(_WIN32)
double rt_f64_sqrt(double value) __asm__("f64.sqrt");
double rt_f64_floor(double value) __asm__("f64.floor");
double rt_f64_ceil(double value) __asm__("f64.ceil");
double rt_f64_sqrt(double value) { return sqrt(value); }
double rt_f64_floor(double value) { return floor(value); }
double rt_f64_ceil(double value) { return ceil(value); }
#endif

int64_t max(int64_t left, int64_t right) {
    return left > right ? left : right;
}

int32_t rt_package_chmod(const uint8_t* path, uint64_t path_len, int32_t mode) {
#if defined(_WIN32)
    (void)path;
    (void)path_len;
    (void)mode;
    return 0;
#else
    if (!path || path_len == 0 || path_len >= 4096) return -1;
    char buffer[4096];
    memcpy(buffer, path, (size_t)path_len);
    buffer[path_len] = '\0';
    return chmod(buffer, (mode_t)mode) == 0 ? 0 : -1;
#endif
}

/* ================================================================
 * Wall-clock, calendar, and system singles for the sffi/system externs
 * (src/lib/nogc_sync_mut/sffi/system.spl, io/time_ops.spl).
 *
 * These 18 names previously existed only as interpreter shims (and 17 of
 * them not even there), so every native link left them unresolved -- the
 * Stage 2 Windows link failed on exactly this set. See
 * doc/08_tracking/bug/stage2_windows_unresolved_inventory_2026-08-31.md
 * group D plus the rt_cpu_count / rt_uuid_v4 singles of group I.
 *
 * Unit contract (pinned here because some functions have zero in-tree
 * callers and the .spl doc comments are the only other contract):
 *   - rt_time_now                : whole SECONDS since the Unix epoch (UTC).
 *   - rt_time_now_unix_millis,
 *     rt_time_millis             : WALL-CLOCK milliseconds since the epoch.
 *     (system.spl calls rt_time_millis "monotonic or wall-clock"; wall is
 *     chosen so it agrees with rt_time_ms / rt_time_now_unix_millis.)
 *   - rt_timestamp_*             : MICROSECONDS since the Unix epoch, the
 *     same unit as rt_timestamp_get_* / the calendar oracle.
 *   - rt_time_format             : ts is whole SECONDS since the epoch.
 *   - rt_time_year..second       : LOCAL time components of now.
 *
 * Calendar arithmetic is pure integer civil-calendar math copied from
 * src/runtime/test/runtime_timestamp_calendar_oracle.c so the results agree
 * with rt_timestamp_get_* on every platform, including pre-1970 values that
 * Windows CRT gmtime/_mkgmtime reject. Only the local-time family touches
 * the CRT (localtime_s / localtime_r).
 *
 * `text` ABI: none of these names appear in text_arg_indices
 * (src/compiler/50.mir/text_extern_abi.spl), so a text argument arrives as a
 * single tagged runtime value (decode via rt_string_data / rt_string_len)
 * and a text return is a tagged value built by rt_string_new -- the
 * rt_shell_exec convention. Failure returns for text-returning functions are
 * the empty string, per the facade's "empty text is failure" contracts.
 * ================================================================ */

#include <stdio.h>
#include <time.h>
#if !defined(_WIN32)
#include <fcntl.h>
#endif

static int64_t core_host_floor_div(int64_t value, int64_t divisor) {
    int64_t quotient = value / divisor;
    if ((value % divisor) != 0 && ((value < 0) != (divisor < 0))) quotient--;
    return quotient;
}

/* Civil-calendar conversions (Howard Hinnant's algorithms, same source as
 * runtime_timestamp_calendar_oracle.c -- keep result-compatible with it). */
static void core_host_days_to_ymd(int64_t z, int64_t* year, int64_t* month, int64_t* day) {
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
    *year = y;
    *month = m;
    *day = d;
}

static int64_t core_host_ymd_to_days(int64_t year, int64_t month, int64_t day) {
    int64_t y = year - (month <= 2 ? 1 : 0);
    int64_t m = month + (month <= 2 ? 9 : -3);
    int64_t era = (y >= 0 ? y : y - 399) / 400;
    int64_t yoe = y - era * 400;
    int64_t doy = (153 * m + 2) / 5 + day - 1;
    int64_t doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + doe - 719468;
}

typedef struct {
    int64_t year, month, day, hour, minute, second, microsecond;
} CoreHostCivilTime;

static void core_host_micros_to_civil(int64_t micros, CoreHostCivilTime* out) {
    int64_t days = core_host_floor_div(micros, 86400000000LL);
    int64_t tod = micros - days * 86400000000LL; /* 0..86399999999 */
    core_host_days_to_ymd(days, &out->year, &out->month, &out->day);
    out->hour = tod / 3600000000LL;
    out->minute = (tod / 60000000LL) % 60;
    out->second = (tod / 1000000LL) % 60;
    out->microsecond = tod % 1000000LL;
}

/* Copy a tagged text argument into buf as a NUL-terminated C string.
 * Returns 0 when the value is not a text or does not fit. */
static int core_host_text_arg(int64_t value, char* buf, size_t buf_size) {
    int64_t len = rt_string_len(value);
    if (len < 0 || (uint64_t)len >= buf_size) return 0;
    const uint8_t* data = rt_string_data(value);
    if (!data && len != 0) return 0;
    if (len != 0) memcpy(buf, data, (size_t)len);
    buf[(size_t)len] = '\0';
    return 1;
}

static int64_t core_host_text_result(const char* s) {
    if (!s) return rt_string_new(NULL, 0);
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

/* ---- Wall clock ---- */

int64_t rt_time_now(void) {
    int64_t micros = rt_time_now_unix_micros();
    return micros < 0 ? -1 : core_host_floor_div(micros, 1000000LL);
}

int64_t rt_time_now_unix_millis(void) {
    int64_t micros = rt_time_now_unix_micros();
    return micros < 0 ? -1 : core_host_floor_div(micros, 1000LL);
}

int64_t rt_time_millis(void) {
    return rt_time_now_unix_millis();
}

/* ---- Local-time components of now (-1 on clock/CRT failure) ---- */

static int core_host_local_now(struct tm* out) {
    time_t now = time(NULL);
    if (now == (time_t)-1) return 0;
#if defined(_WIN32)
    return localtime_s(out, &now) == 0;
#else
    return localtime_r(&now, out) != NULL;
#endif
}

int64_t rt_time_year(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_year + 1900 : -1;
}
int64_t rt_time_month(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_mon + 1 : -1;
}
int64_t rt_time_day(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_mday : -1;
}
int64_t rt_time_hour(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_hour : -1;
}
int64_t rt_time_minute(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_min : -1;
}
int64_t rt_time_second(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_sec : -1;
}

/* ---- Timestamp (micros) -> text ---- */

static void core_host_format_civil(const CoreHostCivilTime* ct, char sep,
                                   int with_zone, char* buf, size_t buf_size) {
    size_t used = (size_t)snprintf(buf, buf_size,
        "%04lld-%02lld-%02lld%c%02lld:%02lld:%02lld",
        (long long)ct->year, (long long)ct->month, (long long)ct->day, sep,
        (long long)ct->hour, (long long)ct->minute, (long long)ct->second);
    if (used >= buf_size) return;
    if (ct->microsecond != 0) {
        used += (size_t)snprintf(buf + used, buf_size - used, ".%06lld",
                                 (long long)ct->microsecond);
        if (used >= buf_size) return;
    }
    if (with_zone) snprintf(buf + used, buf_size - used, "Z");
}

int64_t rt_timestamp_to_iso(int64_t micros) {
    CoreHostCivilTime ct;
    char buf[64];
    core_host_micros_to_civil(micros, &ct);
    core_host_format_civil(&ct, 'T', 1, buf, sizeof(buf));
    return core_host_text_result(buf);
}

int64_t rt_timestamp_to_string(int64_t micros) {
    CoreHostCivilTime ct;
    char buf[64];
    core_host_micros_to_civil(micros, &ct);
    core_host_format_civil(&ct, ' ', 0, buf, sizeof(buf));
    return core_host_text_result(buf);
}

int64_t rt_time_now_iso(void) {
    int64_t micros = rt_time_now_unix_micros();
    if (micros < 0) return rt_string_new(NULL, 0);
    /* Whole-second resolution: the current-time ISO text is a display value. */
    return rt_timestamp_to_iso(core_host_floor_div(micros, 1000000LL) * 1000000LL);
}

/* ---- text -> timestamp (micros; -1 on malformed input) ---- */

static int core_host_scan_digits(const char** cursor, int min_digits,
                                 int max_digits, int64_t* out) {
    const char* p = *cursor;
    int64_t value = 0;
    int count = 0;
    while (count < max_digits && *p >= '0' && *p <= '9') {
        value = value * 10 + (*p - '0');
        p++;
        count++;
    }
    if (count < min_digits) return 0;
    *cursor = p;
    *out = value;
    return 1;
}

/* Accepts: YYYY-MM-DD, optionally followed by ('T'|'t'|' ') HH:MM:SS,
 * optionally .fraction (truncated to micros), optionally 'Z'|'z' or a
 * +HH:MM / -HH[:]MM offset (applied). Leading '-' year sign is accepted. */
static int64_t core_host_parse_timestamp(const char* s) {
    const char* p = s;
    int64_t year, month, day;
    int64_t hour = 0, minute = 0, second = 0, fraction = 0;
    int negative_year = 0;
    if (*p == '-') { negative_year = 1; p++; }
    if (!core_host_scan_digits(&p, 4, 6, &year)) return -1;
    if (negative_year) year = -year;
    if (*p != '-') return -1;
    p++;
    if (!core_host_scan_digits(&p, 2, 2, &month)) return -1;
    if (*p != '-') return -1;
    p++;
    if (!core_host_scan_digits(&p, 2, 2, &day)) return -1;
    if (month < 1 || month > 12 || day < 1) return -1;
    {
        static const int64_t month_days[12] = {31, 28, 31, 30, 31, 30,
                                               31, 31, 30, 31, 30, 31};
        int64_t day_limit = month_days[month - 1];
        if (month == 2 &&
            (year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)))
            day_limit = 29;
        if (day > day_limit) return -1;
    }
    if (*p == 'T' || *p == 't' || *p == ' ') {
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &hour)) return -1;
        if (*p != ':') return -1;
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &minute)) return -1;
        if (*p != ':') return -1;
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &second)) return -1;
        if (hour > 23 || minute > 59 || second > 60) return -1;
        if (*p == '.') {
            p++;
            int64_t scale = 100000;
            int digits = 0;
            while (*p >= '0' && *p <= '9') {
                if (digits < 6) {
                    fraction += (int64_t)(*p - '0') * scale;
                    scale /= 10;
                }
                digits++;
                p++;
            }
            if (digits == 0) return -1;
        }
    }
    int64_t offset_seconds = 0;
    if (*p == 'Z' || *p == 'z') {
        p++;
    } else if (*p == '+' || *p == '-') {
        int64_t sign = *p == '+' ? 1 : -1;
        int64_t off_hour, off_minute = 0;
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &off_hour)) return -1;
        if (*p == ':') {
            p++;
            if (!core_host_scan_digits(&p, 2, 2, &off_minute)) return -1;
        } else if (*p >= '0' && *p <= '9' &&
                   !core_host_scan_digits(&p, 2, 2, &off_minute)) {
            return -1;
        }
        if (off_hour > 23 || off_minute > 59) return -1;
        offset_seconds = sign * (off_hour * 3600 + off_minute * 60);
    }
    if (*p != '\0') return -1;
    int64_t days = core_host_ymd_to_days(year, month, day);
    int64_t secs = days * 86400LL + hour * 3600 + minute * 60 + second
                 - offset_seconds;
    return secs * 1000000LL + fraction;
}

int64_t rt_timestamp_from_iso(int64_t iso_value) {
    char buf[128];
    if (!core_host_text_arg(iso_value, buf, sizeof(buf))) return -1;
    return core_host_parse_timestamp(buf);
}

int64_t rt_timestamp_parse(int64_t text_value) {
    return rt_timestamp_from_iso(text_value);
}

/* Floor difference in whole seconds between two micros timestamps. */
int64_t rt_timestamp_diff_seconds(int64_t a, int64_t b) {
    return core_host_floor_div(a - b, 1000000LL);
}

/* ---- rt_time_format: strftime-subset formatter over UTC ----
 * ts is whole seconds since the epoch. Deliberately NOT CRT strftime: the
 * Windows UCRT parameter-validates unknown specifiers and aborts the
 * process, which would turn a bad format string into a crash. Supported:
 * %Y %m %d %H %M %S %F (=%Y-%m-%d) %T (=%H:%M:%S) %%. Any other specifier
 * fails closed to the empty string. */
int64_t rt_time_format(int64_t ts_seconds, int64_t fmt_value) {
    char fmt[256];
    if (!core_host_text_arg(fmt_value, fmt, sizeof(fmt))) return rt_string_new(NULL, 0);
    if (ts_seconds > INT64_MAX / 1000000LL || ts_seconds < INT64_MIN / 1000000LL)
        return rt_string_new(NULL, 0);
    CoreHostCivilTime ct;
    core_host_micros_to_civil(ts_seconds * 1000000LL, &ct);
    char out[512];
    size_t used = 0;
    const char* p = fmt;
    for (; *p != '\0'; p++) {
        char piece[40];
        if (*p == '%') {
            p++;
            switch (*p) {
                case 'Y': snprintf(piece, sizeof(piece), "%04lld", (long long)ct.year); break;
                case 'm': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.month); break;
                case 'd': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.day); break;
                case 'H': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.hour); break;
                case 'M': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.minute); break;
                case 'S': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.second); break;
                case 'F': snprintf(piece, sizeof(piece), "%04lld-%02lld-%02lld",
                                   (long long)ct.year, (long long)ct.month, (long long)ct.day); break;
                case 'T': snprintf(piece, sizeof(piece), "%02lld:%02lld:%02lld",
                                   (long long)ct.hour, (long long)ct.minute, (long long)ct.second); break;
                case '%': piece[0] = '%'; piece[1] = '\0'; break;
                default: return rt_string_new(NULL, 0);
            }
        } else {
            piece[0] = *p;
            piece[1] = '\0';
        }
        size_t piece_len = strlen(piece);
        if (used + piece_len >= sizeof(out)) return rt_string_new(NULL, 0);
        memcpy(out + used, piece, piece_len);
        used += piece_len;
    }
    return rt_string_new((const uint8_t*)out, (uint64_t)used);
}

/* ---- System singles ---- */

int64_t rt_cpu_count(void) {
#if defined(_WIN32)
    SYSTEM_INFO info;
    GetSystemInfo(&info);
    return info.dwNumberOfProcessors > 0 ? (int64_t)info.dwNumberOfProcessors : -1;
#else
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? (int64_t)count : -1;
#endif
}

/* OS CSPRNG fill -- same provider shape as rt_random_hex in runtime_native.c
 * (BCryptGenRandom via bcrypt.dll on Windows, /dev/urandom elsewhere).
 * Returns 0 on failure; never degrades to a weak source. */
static int core_host_entropy(unsigned char* out, size_t len) {
#if defined(_WIN32)
    typedef long (WINAPI *BCryptGenRandomFn)(void*, unsigned char*, unsigned long, unsigned long);
    if (len > 0xffffffffu) return 0;
    HMODULE library = LoadLibraryA("bcrypt.dll");
    if (!library) return 0;
    BCryptGenRandomFn fill = (BCryptGenRandomFn)GetProcAddress(library, "BCryptGenRandom");
    long status = fill ? fill(NULL, out, (unsigned long)len, 0x00000002) : -1;
    FreeLibrary(library);
    return status == 0;
#else
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd < 0) return 0;
    size_t offset = 0;
    while (offset < len) {
        ssize_t count = read(fd, out + offset, len - offset);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) { close(fd); return 0; }
        offset += (size_t)count;
    }
    close(fd);
    return 1;
#endif
}

/* RFC 4122 version-4 UUID from the OS CSPRNG, lowercase 8-4-4-4-12.
 * Empty text on entropy failure (the facade treats empty as failure). */
int64_t rt_uuid_v4(void) {
    unsigned char bytes[16];
    if (!core_host_entropy(bytes, sizeof(bytes))) return rt_string_new(NULL, 0);
    bytes[6] = (unsigned char)(0x40 | (bytes[6] & 0x0f));
    bytes[8] = (unsigned char)(0x80 | (bytes[8] & 0x3f));
    char buf[37];
    snprintf(buf, sizeof(buf),
        "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5],
        bytes[6], bytes[7], bytes[8], bytes[9], bytes[10], bytes[11],
        bytes[12], bytes[13], bytes[14], bytes[15]);
    return rt_string_new((const uint8_t*)buf, 36u);
}
