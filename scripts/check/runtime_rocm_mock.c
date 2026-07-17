#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct MockProgram {
    char *source;
} MockProgram;

static _Thread_local int current_device;

int hipInit(unsigned flags) { return flags == 0 ? 0 : 1; }
int hipGetDeviceCount(int *count) { if (!count) return 1; *count = 1; return 0; }
int hipDeviceGet(int *device, int ordinal) {
    if (!device || ordinal != 0) return 1;
    *device = ordinal;
    return 0;
}
int hipDeviceGetName(char *name, int len, int device) {
    static const char value[] = "Mock AMD GPU";
    if (!name || len < (int)sizeof(value) || device != 0) return 1;
    memcpy(name, value, sizeof(value));
    return 0;
}
int hipDeviceTotalMem(size_t *bytes, int device) {
    if (!bytes || device != 0) return 1;
    *bytes = (size_t)8 << 30;
    return 0;
}
int hipDeviceGetUuid(void *uuid, int device) {
    static const uint8_t value[16] = {
        0x10, 0x32, 0x54, 0x76, 0x98, 0xba, 0xdc, 0xfe,
        0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef
    };
    if (!uuid || device != 0) return 1;
    memcpy(uuid, value, sizeof(value));
    return 0;
}
int hipSetDevice(int device) {
    if (device != 0) return 1;
    current_device = device;
    return 0;
}
int hipGetDevice(int *device) { if (!device) return 1; *device = current_device; return 0; }
int hipMalloc(void **ptr, size_t size) {
    if (!ptr || size == 0) return 1;
    *ptr = malloc(size);
    return *ptr ? 0 : 2;
}
int hipFree(void *ptr) { free(ptr); return ptr ? 0 : 1; }
int hipMemcpy(void *dst, const void *src, size_t size, int kind) {
    if (!dst || !src || size == 0 || kind < 1 || kind > 3) return 1;
    memcpy(dst, src, size);
    return 0;
}
int hipMemset(void *ptr, int value, size_t size) {
    if (!ptr || size == 0) return 1;
    memset(ptr, value, size);
    return 0;
}
int hipModuleLoadData(void **module, const void *image) {
    if (!module || !image) return 1;
    *module = malloc(1);
    return *module ? 0 : 2;
}
int hipModuleGetFunction(void **function, void *module, const char *name) {
    if (!function || !module || !name || strcmp(name, "mock_kernel") != 0) return 1;
    *function = module;
    return 0;
}
int hipModuleLaunchKernel(void *function, unsigned gx, unsigned gy, unsigned gz,
                          unsigned bx, unsigned by, unsigned bz, unsigned shared,
                          void *stream, void **params, void **extra) {
    (void)stream;
    (void)extra;
    if (!function || gx != 1 || gy != 1 || gz != 1 || bx != 1 || by != 1 || bz != 1 || shared != 0) return 1;
    if (!params || *(int64_t *)params[0] != 17 || *(int64_t *)params[1] != 29) return 1;
    return 0;
}
int hipModuleUnload(void *module) { free(module); return module ? 0 : 1; }
int hipDeviceSynchronize(void) { return 0; }
int hipStreamCreate(void **stream) {
    if (!stream) return 1;
    *stream = malloc(1);
    return *stream ? 0 : 2;
}
int hipStreamDestroy(void *stream) { free(stream); return stream ? 0 : 1; }
int hipStreamSynchronize(void *stream) { return stream ? 0 : 1; }
int hipGetLastError(void) { return 0; }
const char *hipGetErrorString(int error) { return error == 0 ? "mock success" : "mock failure"; }

int hiprtcCreateProgram(void **program, const char *source, const char *name,
                        int header_count, const char **headers, const char **include_names) {
    (void)name;
    (void)headers;
    (void)include_names;
    if (!program || !source || header_count != 0) return 1;
    MockProgram *p = calloc(1, sizeof(*p));
    if (!p) return 2;
    p->source = strdup(source);
    if (!p->source) { free(p); return 2; }
    *program = p;
    return 0;
}
int hiprtcCompileProgram(void *program, int option_count, const char **options) {
    (void)options;
    MockProgram *p = program;
    return p && p->source && strstr(p->source, "mock_kernel") && option_count == 0 ? 0 : 1;
}
int hiprtcGetCodeSize(void *program, size_t *size) {
    if (!program || !size) return 1;
    *size = 8;
    return 0;
}
int hiprtcGetCode(void *program, char *code) {
    static const char image[8] = {'M','O','C','K','C','O','D','E'};
    if (!program || !code) return 1;
    memcpy(code, image, sizeof(image));
    return 0;
}
int hiprtcGetProgramLogSize(void *program, size_t *size) {
    if (!program || !size) return 1;
    *size = 1;
    return 0;
}
int hiprtcGetProgramLog(void *program, char *log) {
    if (!program || !log) return 1;
    log[0] = '\0';
    return 0;
}
int hiprtcDestroyProgram(void **program) {
    if (!program || !*program) return 1;
    MockProgram *p = *program;
    free(p->source);
    free(p);
    *program = NULL;
    return 0;
}
