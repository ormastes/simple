#include <stdio.h>
#include <stdlib.h>

#if defined(_WIN32)
#include <windows.h>
#define SIMPLE_EXPORT __declspec(dllexport)
#else
#define SIMPLE_EXPORT __attribute__((visibility("default")))
#endif

static void simple_dynamic_loader_mark_unloaded(void) {
#if defined(_WIN32)
    /* Shared UCRT getenv() reads a process-start snapshot; the spec sets the
     * marker later through the Win32 environment, so read that directly. */
    char buffer[1024];
    DWORD length = GetEnvironmentVariableA("SIMPLE_DYNLOADER_UNLOAD_MARKER", buffer, sizeof(buffer));
    const char *path = (length > 0 && length < sizeof(buffer)) ? buffer : NULL;
#else
    const char *path = getenv("SIMPLE_DYNLOADER_UNLOAD_MARKER");
#endif
    if (path != NULL && path[0] != '\0') {
        FILE *file = fopen(path, "wb");
        if (file != NULL) {
            fputs("unloaded\n", file);
            fclose(file);
        }
    }
}

#if defined(_WIN32)
BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {
    (void)instance;
    (void)reserved;
    if (reason == DLL_PROCESS_DETACH) {
        simple_dynamic_loader_mark_unloaded();
    }
    return TRUE;
}
#else
__attribute__((destructor)) static void simple_dynamic_loader_destructor(void) {
    simple_dynamic_loader_mark_unloaded();
}
#endif

SIMPLE_EXPORT int simple_backend_plugin_v1(void) {
    return 1;
}
