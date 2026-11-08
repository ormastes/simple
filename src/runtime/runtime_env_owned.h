#ifndef SIMPLE_RUNTIME_ENV_OWNED_H
#define SIMPLE_RUNTIME_ENV_OWNED_H

#include <stdlib.h>
#include <string.h>

/* Internal snapshot, owned by the caller. Return 0 for a successful lookup,
 * with NULL for absence or an allocated string for a present (possibly empty)
 * value; return -1 with NULL for lookup/allocation failure. Never retain
 * CRT environment storage across another environment lookup or mutation. */
static int rt_env_snapshot(const char* key, char** result) {
    *result = NULL;
    if (!key) return -1;
#if defined(_MSC_VER)
    char* value = NULL;
    size_t length = 0;
    if (_dupenv_s(&value, &length, key) != 0) {
        free(value);
        return -1;
    }
    *result = value;
    return 0;
#else
    const char* value = getenv(key);
    if (!value) return 0;
    size_t length = strlen(value) + 1;
    char* copy = (char*)malloc(length);
    if (copy) memcpy(copy, value, length);
    *result = copy;
    return copy ? 0 : -1;
#endif
}

/* Exact one-byte flag values need no allocation or borrowed CRT storage. */
static char rt_env_flag_value(const char* key) {
#if defined(_MSC_VER)
    char value[2];
    size_t length = 0;
    return getenv_s(&length, value, sizeof(value), key) == 0 &&
        length == 2 ? value[0] : '\0';
#else
    const char* value = getenv(key);
    return value && value[0] && value[1] == '\0' ? value[0] : '\0';
#endif
}

static int rt_env_flag_is(const char* key, char expected) {
    return rt_env_flag_value(key) == expected;
}

static char* rt_env_owned(const char* key) {
    char* value = NULL;
    (void)rt_env_snapshot(key, &value);
    return value;
}

static int rt_env_present(const char* key) {
#if !defined(_MSC_VER)
    return key && getenv(key) != NULL;
#else
    char* value = rt_env_owned(key);
    int present = value != NULL;
    free(value);
    return present;
#endif
}

#endif
