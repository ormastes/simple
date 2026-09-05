#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct MockProgram {
    char *source;
} MockProgram;

typedef struct MockFunction {
    char name[64];
} MockFunction;

typedef struct MockModule {
    MockFunction functions[32];
    size_t function_count;
} MockModule;

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
    *module = calloc(1, sizeof(MockModule));
    return *module ? 0 : 2;
}
int hipModuleGetFunction(void **function, void *module, const char *name) {
    MockModule *m = module;
    if (!function || !m || !name || strlen(name) >= sizeof(m->functions[0].name) ||
        m->function_count >= sizeof(m->functions) / sizeof(m->functions[0])) return 1;
    MockFunction *f = &m->functions[m->function_count++];
    memcpy(f->name, name, strlen(name) + 1);
    *function = f;
    return 0;
}

static int launch_font_atlas(void **params, unsigned gx, unsigned bx) {
    if (!params) return 1;
    for (size_t i = 0; i < 15; ++i) if (!params[i]) return 1;
#define ARG(i) (*(const int64_t *)params[(i)])
    uint32_t *atlas = (uint32_t *)(uintptr_t)ARG(0);
    uint32_t *dst = (uint32_t *)(uintptr_t)ARG(1);
    int64_t aw = ARG(2), ah = ARG(3), ac = ARG(4);
    int64_t ax = ARG(5), ay = ARG(6), qw = ARG(7), qh = ARG(8);
    int64_t dw = ARG(9), dh = ARG(10), dc = ARG(11), dx0 = ARG(12), dy0 = ARG(13);
    uint32_t color = (uint32_t)ARG(14);
#undef ARG
    if (!atlas || !dst || aw <= 0 || ah <= 0 || qw <= 0 || qh <= 0 || dw <= 0 || dh <= 0 ||
        aw > INT_MAX || ah > INT_MAX || qw > INT_MAX || qh > INT_MAX || dw > INT_MAX || dh > INT_MAX ||
        ac != aw * ah || dc != dw * dh || ax < 0 || ay < 0 || ax > aw - qw || ay > ah - qh ||
        (uint64_t)gx * bx < (uint64_t)qw * qh) return 1;
    for (int64_t i = 0; i < qw * qh; ++i) {
        int64_t sx = ax + i % qw, sy = ay + i / qw;
        int64_t dx = dx0 + i % qw, dy = dy0 + i / qw;
        if (dx < 0 || dy < 0 || dx >= dw || dy >= dh) continue;
        uint32_t mask_a = atlas[sy * aw + sx] >> 24;
        uint32_t sa = (mask_a * (color >> 24) + 127) / 255;
        if (sa == 0) continue;
        uint32_t d = dst[dy * dw + dx], inv = 255 - sa;
        uint32_t dst_weight = ((d >> 24) * inv) / 255;
        uint32_t out_a = sa + dst_weight;
        uint32_t out_r = (((color >> 16) & 255) * sa + ((d >> 16) & 255) * dst_weight) / out_a;
        uint32_t out_g = (((color >> 8) & 255) * sa + ((d >> 8) & 255) * dst_weight) / out_a;
        uint32_t out_b = ((color & 255) * sa + (d & 255) * dst_weight) / out_a;
        dst[dy * dw + dx] = (out_a << 24) | (out_r << 16) | (out_g << 8) | out_b;
    }
    return 0;
}

int hipModuleLaunchKernel(void *function, unsigned gx, unsigned gy, unsigned gz,
                          unsigned bx, unsigned by, unsigned bz, unsigned shared,
                          void *stream, void **params, void **extra) {
    (void)stream;
    (void)extra;
    MockFunction *f = function;
    if (!f || gy != 1 || gz != 1 || by != 1 || bz != 1 || shared != 0) return 1;
    if (strcmp(f->name, "mock_kernel") == 0)
        return gx == 1 && bx == 1 && params && *(int64_t *)params[0] == 17 && *(int64_t *)params[1] == 29 ? 0 : 1;
    if (strcmp(f->name, "simple_font_atlas_composite_v1_u32") == 0)
        return launch_font_atlas(params, gx, bx);
    return 1;
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
    if (!p || !p->source || option_count != 0) return 1;
    if (strstr(p->source, "mock_kernel")) return 0;
    return strstr(p->source, "extern \"C\" __global__ void simple_font_atlas_composite_v1_u32(") &&
           strstr(p->source, "const unsigned int* atlas") &&
           strstr(p->source, "unsigned int* dst") &&
           strstr(p->source, "long atlas_width") &&
           strstr(p->source, "long dst_count") &&
           strstr(p->source, "long dst_x, long dst_y, long color") ? 0 : 1;
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
