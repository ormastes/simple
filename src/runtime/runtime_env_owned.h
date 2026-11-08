#ifndef SIMPLE_RUNTIME_ENV_OWNED_H
#define SIMPLE_RUNTIME_ENV_OWNED_H

#include <stdlib.h>
#include <string.h>

/* Internal snapshot, owned by the caller. NULL means absent or allocation
 * failure; a present empty value is an allocated empty string. Never retain
 * CRT environment storage across another environment lookup or mutation. */
static char* rt_env_owned(const char* key) {
    if (!key) return NULL;
#if defined(_MSC_VER)
    char* value = NULL;
    size_t length = 0;
    if (_dupenv_s(&value, &length, key) != 0) {
        free(value);
        return NULL;
    }
    return value;
#else
    const char* value = getenv(key);
    if (!value) return NULL;
    size_t length = strlen(value) + 1;
    char* copy = (char*)malloc(length);
    if (copy) memcpy(copy, value, length);
    return copy;
#endif
}

static int rt_env_present(const char* key) {
    char* value = rt_env_owned(key);
    int present = value != NULL;
    free(value);
    return present;
}

#endif
