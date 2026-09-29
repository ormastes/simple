#if defined(_WIN32)
#define SIMPLE_EXPORT __declspec(dllexport)
#else
#define SIMPLE_EXPORT __attribute__((visibility("default")))
#endif

SIMPLE_EXPORT int simple_backend_plugin_not_v1(void) {
    return 0;
}
