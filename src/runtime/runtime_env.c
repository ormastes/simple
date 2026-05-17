#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

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
