/* Hosted dynamic loading for pure-Simple native binaries. */

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <dlfcn.h>
#endif

#include "runtime.h"

int64_t spl_dlopen(int64_t path_value) {
    const char* path = rt_interp_cstr(path_value);
    if (!path) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)LoadLibraryA(path);
#else
    return (int64_t)(intptr_t)dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}

int64_t spl_dlsym(int64_t handle, int64_t name_value) {
    const char* name = rt_interp_cstr(name_value);
    if (!handle || !name) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)GetProcAddress((HMODULE)(intptr_t)handle, name);
#else
    return (int64_t)(intptr_t)dlsym((void*)(intptr_t)handle, name);
#endif
}

int64_t spl_dlclose(int64_t handle) {
    if (!handle) return 0;
#ifdef _WIN32
    return FreeLibrary((HMODULE)(intptr_t)handle) ? 0 : -1;
#else
    return (int64_t)dlclose((void*)(intptr_t)handle);
#endif
}
