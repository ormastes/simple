#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>

int64_t __c_rt_env_get_i64(const uint8_t *name_ptr, uint64_t name_len, int64_t default_value) {
    if (!name_ptr || name_len == 0) return default_value;
    if (name_len > 4095) return default_value;
    char buf[4096];
    memcpy(buf, name_ptr, (size_t)name_len);
    buf[name_len] = '\0';
    const char *val = getenv(buf);
    if (!val) return default_value;
    char *end;
    long long result = strtoll(val, &end, 10);
    if (end == val) return default_value;
    return (int64_t)result;
}

bool __c_rt_env_set(const uint8_t *name_ptr, uint64_t name_len, const uint8_t *value_ptr, uint64_t value_len) {
    if (!name_ptr || !value_ptr) return false;
    if (name_len > 4095 || value_len > 65535) return false;
    char name_buf[4096];
    memcpy(name_buf, name_ptr, (size_t)name_len);
    name_buf[name_len] = '\0';
    char *value_buf = (char *)malloc((size_t)value_len + 1);
    if (!value_buf) return false;
    memcpy(value_buf, value_ptr, (size_t)value_len);
    value_buf[value_len] = '\0';
    int rc = setenv(name_buf, value_buf, 1);
    free(value_buf);
    return rc == 0;
}

void __c_rt_set_env(const uint8_t *name_ptr, uint64_t name_len, const uint8_t *value_ptr, uint64_t value_len) {
    __c_rt_env_set(name_ptr, name_len, value_ptr, value_len);
}

bool __c_rt_env_exists(const uint8_t *name_ptr, uint64_t name_len) {
    if (!name_ptr || name_len == 0) return false;
    if (name_len > 4095) return false;
    char buf[4096];
    memcpy(buf, name_ptr, (size_t)name_len);
    buf[name_len] = '\0';
    return getenv(buf) != NULL;
}

bool __c_rt_env_remove(const uint8_t *name_ptr, uint64_t name_len) {
    if (!name_ptr || name_len == 0) return false;
    if (name_len > 4095) return false;
    char buf[4096];
    memcpy(buf, name_ptr, (size_t)name_len);
    buf[name_len] = '\0';
    unsetenv(buf);
    return true;
}

void __c_rt_exit(int32_t code) {
    exit(code);
}

int64_t __c_rt_stdout_flush(void) {
    fflush(stdout);
    return 0;
}

int64_t __c_rt_stderr_flush(void) {
    fflush(stderr);
    return 0;
}

int64_t __c_rt_platform_name(const uint8_t **out_ptr) {
#if defined(_WIN32)
    static const uint8_t name[] = "windows";
    *out_ptr = name; return 7;
#elif defined(__APPLE__)
    static const uint8_t name[] = "macos";
    *out_ptr = name; return 5;
#elif defined(__FreeBSD__)
    static const uint8_t name[] = "freebsd";
    *out_ptr = name; return 7;
#elif defined(__linux__)
    static const uint8_t name[] = "linux";
    *out_ptr = name; return 5;
#elif defined(__illumos__)
    static const uint8_t name[] = "illumos";
    *out_ptr = name; return 7;
#elif defined(__sun) && defined(__SVR4)
    static const uint8_t name[] = "solaris";
    *out_ptr = name; return 7;
#else
    static const uint8_t name[] = "unknown";
    *out_ptr = name; return 7;
#endif
}

#if defined(__unix__) || defined(__APPLE__)
#include <sys/ioctl.h>
#include <unistd.h>
#endif

int32_t __c_rt_env_get_str(const uint8_t *name_ptr, uint64_t name_len,
                            const uint8_t **out_ptr, uint64_t *out_len) {
    if (!name_ptr || name_len == 0 || name_len > 4095) return 0;
    char buf[4096];
    memcpy(buf, name_ptr, (size_t)name_len);
    buf[name_len] = '\0';
    const char *val = getenv(buf);
    if (!val) return 0;
    *out_ptr = (const uint8_t *)val;
    *out_len = (uint64_t)strlen(val);
    return 1;
}

int64_t __c_rt_env_cwd(uint8_t *out, uint64_t out_cap) {
    if (!out || out_cap == 0) return 0;
    char *result = getcwd((char *)out, (size_t)out_cap);
    if (!result) return 0;
    return (int64_t)strlen(result);
}

int32_t __c_rt_env_home(const uint8_t **out_ptr, uint64_t *out_len) {
    const char *val = getenv("HOME");
#ifdef _WIN32
    if (!val) val = getenv("USERPROFILE");
#endif
    if (!val) return 0;
    *out_ptr = (const uint8_t *)val;
    *out_len = (uint64_t)strlen(val);
    return 1;
}

int64_t __c_rt_env_temp(uint8_t *out, uint64_t out_cap) {
    const char *val = getenv("TMPDIR");
    if (!val) val = getenv("TMP");
    if (!val) val = getenv("TEMP");
#ifdef _WIN32
    if (!val) val = "C:\\Temp";
#else
    if (!val) val = "/tmp";
#endif
    size_t len = strlen(val);
    if (len >= out_cap) return 0;
    memcpy(out, val, len);
    return (int64_t)len;
}

void __c_rt_term_get_size(int32_t *cols, int32_t *rows) {
    *cols = 80; *rows = 24;
#if defined(__unix__) || defined(__APPLE__)
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0 && ws.ws_row > 0) {
        *cols = (int32_t)ws.ws_col;
        *rows = (int32_t)ws.ws_row;
    }
#elif defined(_WIN32)
    /* Windows: GetConsoleScreenBufferInfo handled in Rust wrapper */
#endif
}
