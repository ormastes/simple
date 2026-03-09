#include <cuda.h>
#include <cstdio>

namespace {

void logError(const char* stage, CUresult res) {
    const char* name = nullptr;
    const char* desc = nullptr;
    cuGetErrorName(res, &name);
    cuGetErrorString(res, &desc);
    std::fprintf(stderr, "ERROR: %s failed: %s (%s)\n", stage,
                 name ? name : "unknown", desc ? desc : "no description");
}

}  // namespace

int main() {
    CUresult res = cuInit(0);
    if (res != CUDA_SUCCESS) {
        logError("cuInit", res);
        return 2;
    }

    CUdevice dev{};
    res = cuDeviceGet(&dev, 0);
    if (res != CUDA_SUCCESS) {
        logError("cuDeviceGet", res);
        return 3;
    }

    CUcontext ctx{};
    res = cuCtxCreate(&ctx, 0, dev);
    if (res != CUDA_SUCCESS) {
        logError("cuCtxCreate", res);
        return 4;
    }

    CUdeviceptr ptr{};
    res = cuMemAlloc(&ptr, 4096);
    if (res != CUDA_SUCCESS) {
        logError("cuMemAlloc", res);
        cuCtxDestroy(ctx);
        return 5;
    }

    CUDA_POINTER_ATTRIBUTE_P2P_TOKENS tokens{};
    res = cuPointerGetAttribute(&tokens, CU_POINTER_ATTRIBUTE_P2P_TOKENS, ptr);
    if (res != CUDA_SUCCESS) {
        logError("cuPointerGetAttribute", res);
        cuMemFree(ptr);
        cuCtxDestroy(ctx);
        return 6;
    }

    std::printf("p2p_token=0x%llx va_space=0x%x\n",
                static_cast<unsigned long long>(tokens.p2pToken),
                static_cast<unsigned int>(tokens.vaSpaceToken));

    cuMemFree(ptr);
    cuCtxDestroy(ctx);

    if (tokens.p2pToken == 0) {
        std::fprintf(stderr,
                     "P2P token is 0. NVIDIA driver is not exposing peer tokens; "
                     "GPU P2P mappings will not work.\n");
        return 10;
    }

    return 0;
}
