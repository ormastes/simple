/* Vulkan Compute Perf Benchmark — via libvulkan.so
 * Tests vkCmdFillBuffer (GPU buffer fill, analog of CUDA cuMemsetD32).
 * Compile: gcc -O2 -o vulkan_bench vulkan_bench.c -ldl -lrt
 * Run:     ./vulkan_bench
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <dlfcn.h>
#include <stdint.h>

/* Minimal Vulkan types */
typedef uint32_t VkResult;
typedef uint32_t VkBool32;
typedef uint32_t VkFlags;
typedef uint64_t VkDeviceSize;

typedef struct VkInstance_T*        VkInstance;
typedef struct VkPhysicalDevice_T*  VkPhysicalDevice;
typedef struct VkDevice_T*          VkDevice;
typedef struct VkQueue_T*           VkQueue;
typedef struct VkCommandPool_T*     VkCommandPool;
typedef struct VkCommandBuffer_T*   VkCommandBuffer;
typedef struct VkBuffer_T*          VkBuffer;
typedef struct VkDeviceMemory_T*    VkDeviceMemory;
typedef struct VkFence_T*           VkFence;

typedef struct {
    uint32_t sType; const void* pNext; uint32_t flags;
    const void* pApplicationInfo; uint32_t enabledLayerCount;
    const char* const* ppEnabledLayerNames; uint32_t enabledExtensionCount;
    const char* const* ppEnabledExtensionNames;
} VkInstanceCreateInfo;

typedef struct {
    uint32_t sType; const void* pNext; VkFlags flags;
    uint32_t queueFamilyIndex; uint32_t queueCount;
    const float* pQueuePriorities;
} VkDeviceQueueCreateInfo;

typedef struct {
    uint32_t sType; const void* pNext; VkFlags flags;
    uint32_t queueCreateInfoCount;
    const VkDeviceQueueCreateInfo* pQueueCreateInfos;
    uint32_t enabledLayerCount; const char* const* ppEnabledLayerNames;
    uint32_t enabledExtensionCount; const char* const* ppEnabledExtensionNames;
    const void* pEnabledFeatures;
} VkDeviceCreateInfo;

typedef struct {
    uint32_t sType; const void* pNext; VkFlags flags;
    VkDeviceSize size; VkFlags usage; uint32_t sharingMode;
    uint32_t queueFamilyIndexCount; const uint32_t* pQueueFamilyIndices;
} VkBufferCreateInfo;

typedef struct { VkDeviceSize size; VkDeviceSize alignment; uint32_t memoryTypeBits; } VkMemoryRequirements;
typedef struct { VkFlags propertyFlags; uint32_t heapIndex; } VkMemoryType;
typedef struct { VkDeviceSize size; VkFlags flags; } VkMemoryHeap;
typedef struct { uint32_t memoryTypeCount; VkMemoryType memoryTypes[32]; uint32_t memoryHeapCount; VkMemoryHeap memoryHeaps[16]; } VkPhysicalDeviceMemoryProperties;
typedef struct { uint32_t sType; const void* pNext; VkDeviceSize allocationSize; uint32_t memoryTypeIndex; } VkMemoryAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t queueFamilyIndex; } VkCommandPoolCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkCommandPool commandPool; uint32_t level; uint32_t commandBufferCount; } VkCommandBufferAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; const void* pInheritanceInfo; } VkCommandBufferBeginInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; } VkFenceCreateInfo;

typedef struct {
    uint32_t sType; const void* pNext;
    uint32_t waitSemaphoreCount; const void* pWaitSemaphores; const VkFlags* pWaitDstStageMask;
    uint32_t commandBufferCount; const VkCommandBuffer* pCommandBuffers;
    uint32_t signalSemaphoreCount; const void* pSignalSemaphores;
} VkSubmitInfo;

/* Function pointer types */
typedef VkResult (*PFN_vkCreateInstance)(const VkInstanceCreateInfo*, const void*, VkInstance*);
typedef void     (*PFN_vkDestroyInstance)(VkInstance, const void*);
typedef VkResult (*PFN_vkEnumeratePhysicalDevices)(VkInstance, uint32_t*, VkPhysicalDevice*);
typedef void     (*PFN_vkGetPhysicalDeviceProperties)(VkPhysicalDevice, void*);
typedef void     (*PFN_vkGetPhysicalDeviceMemoryProperties)(VkPhysicalDevice, VkPhysicalDeviceMemoryProperties*);
typedef VkResult (*PFN_vkCreateDevice)(VkPhysicalDevice, const VkDeviceCreateInfo*, const void*, VkDevice*);
typedef void     (*PFN_vkDestroyDevice)(VkDevice, const void*);
typedef void     (*PFN_vkGetDeviceQueue)(VkDevice, uint32_t, uint32_t, VkQueue*);
typedef VkResult (*PFN_vkCreateBuffer)(VkDevice, const VkBufferCreateInfo*, const void*, VkBuffer*);
typedef void     (*PFN_vkDestroyBuffer)(VkDevice, VkBuffer, const void*);
typedef void     (*PFN_vkGetBufferMemoryRequirements)(VkDevice, VkBuffer, VkMemoryRequirements*);
typedef VkResult (*PFN_vkAllocateMemory)(VkDevice, const VkMemoryAllocateInfo*, const void*, VkDeviceMemory*);
typedef void     (*PFN_vkFreeMemory)(VkDevice, VkDeviceMemory, const void*);
typedef VkResult (*PFN_vkBindBufferMemory)(VkDevice, VkBuffer, VkDeviceMemory, VkDeviceSize);
typedef VkResult (*PFN_vkMapMemory)(VkDevice, VkDeviceMemory, VkDeviceSize, VkDeviceSize, VkFlags, void**);
typedef void     (*PFN_vkUnmapMemory)(VkDevice, VkDeviceMemory);
typedef VkResult (*PFN_vkCreateCommandPool)(VkDevice, const VkCommandPoolCreateInfo*, const void*, VkCommandPool*);
typedef void     (*PFN_vkDestroyCommandPool)(VkDevice, VkCommandPool, const void*);
typedef VkResult (*PFN_vkAllocateCommandBuffers)(VkDevice, const VkCommandBufferAllocateInfo*, VkCommandBuffer*);
typedef VkResult (*PFN_vkBeginCommandBuffer)(VkCommandBuffer, const VkCommandBufferBeginInfo*);
typedef VkResult (*PFN_vkEndCommandBuffer)(VkCommandBuffer);
typedef void     (*PFN_vkCmdFillBuffer)(VkCommandBuffer, VkBuffer, VkDeviceSize, VkDeviceSize, uint32_t);
typedef VkResult (*PFN_vkCreateFence)(VkDevice, const VkFenceCreateInfo*, const void*, VkFence*);
typedef void     (*PFN_vkDestroyFence)(VkDevice, VkFence, const void*);
typedef VkResult (*PFN_vkResetFences)(VkDevice, uint32_t, const VkFence*);
typedef VkResult (*PFN_vkQueueSubmit)(VkQueue, uint32_t, const VkSubmitInfo*, VkFence);
typedef VkResult (*PFN_vkWaitForFences)(VkDevice, uint32_t, const VkFence*, VkBool32, uint64_t);
typedef VkResult (*PFN_vkDeviceWaitIdle)(VkDevice);

#define DLSYM(h, name) (PFN_##name)dlsym(h, #name)

static long long now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static void* (*volatile measured_memset)(void*, int, size_t) = memset;
static void* (*volatile measured_memcpy)(void*, const void*, size_t) = memcpy;

static int offload_preferred(long long cpu_ns, long long device_ns) {
    return cpu_ns > 0 && device_ns > 0 && cpu_ns >= device_ns &&
        cpu_ns - device_ns >= device_ns / 2 + device_ns % 2;
}

static int compare_u64(const void* a, const void* b) {
    uint64_t av = *(const uint64_t*)a, bv = *(const uint64_t*)b;
    return av < bv ? -1 : av > bv;
}

static uint32_t env_u32(const char* name, uint32_t fallback, uint32_t maximum) {
    const char* raw = getenv(name);
    if (!raw || !*raw) return fallback;
    char* end = NULL;
    unsigned long value = strtoul(raw, &end, 10);
    if (!end || *end || value == 0 || value > maximum) return fallback;
    return (uint32_t)value;
}

static int self_test(void) {
    unsigned char buf[8] = {0};
    struct timespec delay = { .tv_nsec = 1000000 };
    long long started = now_ns();
    nanosleep(&delay, NULL);
    measured_memset(buf, 0x1E, sizeof(buf));
    if (now_ns() <= started || buf[0] != 0x1E || buf[7] != 0x1E ||
            !offload_preferred(150, 100) || offload_preferred(149, 100) ||
            !offload_preferred(152, 101) || offload_preferred(151, 101)) {
        printf("vulkan_bench_self_test=fail\n");
        return 1;
    }
    printf("vulkan_bench_self_test=pass\n");
    return 0;
}

static int32_t find_mem_type(const VkPhysicalDeviceMemoryProperties* p, uint32_t bits, VkFlags flags) {
    for (uint32_t i = 0; i < p->memoryTypeCount; i++)
        if ((bits & (1u << i)) && (p->memoryTypes[i].propertyFlags & flags) == flags)
            return (int32_t)i;
    return -1;
}

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--self-test") == 0) return self_test();

    printf("========================================\n");
    printf("Vulkan GPU Bench (vkCmdFillBuffer)\n");
    printf("========================================\n");

    void* lib = dlopen("libvulkan.so.1", RTLD_LAZY);
    if (!lib) lib = dlopen("libvulkan.so", RTLD_LAZY);
    if (!lib) { printf("FAIL: cannot load libvulkan.so\n"); return 1; }

    PFN_vkCreateInstance                 f_ci  = DLSYM(lib, vkCreateInstance);
    PFN_vkDestroyInstance                f_di  = DLSYM(lib, vkDestroyInstance);
    PFN_vkEnumeratePhysicalDevices       f_epd = DLSYM(lib, vkEnumeratePhysicalDevices);
    PFN_vkGetPhysicalDeviceProperties    f_gpp = DLSYM(lib, vkGetPhysicalDeviceProperties);
    PFN_vkGetPhysicalDeviceMemoryProperties f_gmp = DLSYM(lib, vkGetPhysicalDeviceMemoryProperties);
    PFN_vkCreateDevice                   f_cd  = DLSYM(lib, vkCreateDevice);
    PFN_vkDestroyDevice                  f_dd  = DLSYM(lib, vkDestroyDevice);
    PFN_vkGetDeviceQueue                 f_gdq = DLSYM(lib, vkGetDeviceQueue);
    PFN_vkCreateBuffer                   f_cb  = DLSYM(lib, vkCreateBuffer);
    PFN_vkDestroyBuffer                  f_db  = DLSYM(lib, vkDestroyBuffer);
    PFN_vkGetBufferMemoryRequirements    f_gmr = DLSYM(lib, vkGetBufferMemoryRequirements);
    PFN_vkAllocateMemory                 f_am  = DLSYM(lib, vkAllocateMemory);
    PFN_vkFreeMemory                     f_fm  = DLSYM(lib, vkFreeMemory);
    PFN_vkBindBufferMemory               f_bbm = DLSYM(lib, vkBindBufferMemory);
    PFN_vkMapMemory                      f_mm  = DLSYM(lib, vkMapMemory);
    PFN_vkUnmapMemory                    f_um  = DLSYM(lib, vkUnmapMemory);
    PFN_vkCreateCommandPool              f_ccp = DLSYM(lib, vkCreateCommandPool);
    PFN_vkDestroyCommandPool             f_dcp = DLSYM(lib, vkDestroyCommandPool);
    PFN_vkAllocateCommandBuffers         f_acb = DLSYM(lib, vkAllocateCommandBuffers);
    PFN_vkBeginCommandBuffer             f_bcb = DLSYM(lib, vkBeginCommandBuffer);
    PFN_vkEndCommandBuffer               f_ecb = DLSYM(lib, vkEndCommandBuffer);
    PFN_vkCmdFillBuffer                  f_cfb = DLSYM(lib, vkCmdFillBuffer);
    PFN_vkCreateFence                    f_cf  = DLSYM(lib, vkCreateFence);
    PFN_vkDestroyFence                   f_df  = DLSYM(lib, vkDestroyFence);
    PFN_vkResetFences                    f_rf  = DLSYM(lib, vkResetFences);
    PFN_vkQueueSubmit                    f_qs  = DLSYM(lib, vkQueueSubmit);
    PFN_vkWaitForFences                  f_wf  = DLSYM(lib, vkWaitForFences);
    PFN_vkDeviceWaitIdle                 f_dwi = DLSYM(lib, vkDeviceWaitIdle);

    if (!f_ci || !f_cd || !f_cfb || !f_qs) {
        printf("FAIL: missing Vulkan symbols\n"); return 1;
    }

    /* --- Instance --- */
    VkInstanceCreateInfo ici = { .sType = 1 };
    VkInstance instance = NULL;
    long long t0 = now_ns();
    VkResult res = f_ci(&ici, NULL, &instance);
    double init_ms = (double)(now_ns() - t0) / 1000000.0;
    if (res) { printf("FAIL: vkCreateInstance = %u\n", res); return 1; }
    printf("  Instance created: %.3f ms\n", init_ms);

    /* --- Enumerate --- */
    uint32_t dev_count = 0;
    f_epd(instance, &dev_count, NULL);
    printf("  Physical devices: %u\n", dev_count);
    if (!dev_count) { printf("FAIL: no devices\n"); return 1; }

    VkPhysicalDevice* devs = calloc(dev_count, sizeof(VkPhysicalDevice));
    f_epd(instance, &dev_count, devs);
    VkPhysicalDevice phys = devs[0];

    uint32_t selected_device_type = 0;
    char selected_device_name[256] = "unknown";
    if (f_gpp) {
        for (uint32_t i = 0; i < dev_count && i < 4; i++) {
            char props[1024] = {0};
            f_gpp(devs[i], props);
            printf("    Device %u: %s\n", i, props + 20);
            if (i == 0) {
                memcpy(&selected_device_type, props + 16, sizeof(uint32_t));
                memcpy(selected_device_name, props + 20,
                       sizeof(selected_device_name) - 1);
                selected_device_name[sizeof(selected_device_name) - 1] = '\0';
            }
        }
    }
    free(devs);

    /* --- Logical device (queue family 0) --- */
    float prio = 1.0f;
    VkDeviceQueueCreateInfo dqci = { .sType = 2, .queueCount = 1, .pQueuePriorities = &prio };
    VkDeviceCreateInfo dci = { .sType = 3, .queueCreateInfoCount = 1, .pQueueCreateInfos = &dqci };
    VkDevice dev = NULL;
    res = f_cd(phys, &dci, NULL, &dev);
    if (res) { printf("FAIL: vkCreateDevice = %u\n", res); return 1; }
    printf("  Logical device: OK\n");

    VkQueue queue = NULL;
    f_gdq(dev, 0, 0, &queue);

    /* --- Configurable framebuffer-sized storage+transfer buffer --- */
    uint32_t width = env_u32("VULKAN_BENCH_WIDTH", 1920, 16384);
    uint32_t height = env_u32("VULKAN_BENCH_HEIGHT", 1080, 16384);
    uint32_t iterations = env_u32("VULKAN_BENCH_ITERATIONS", 100, 1000);
    uint32_t active_basis_points = env_u32(
        "VULKAN_BENCH_ACTIVE_BASIS_POINTS", 10000, 10000);
    uint64_t pixel_count = (uint64_t)width * height;
    if (pixel_count > UINT32_MAX) { printf("FAIL: pixel count overflow\n"); return 1; }
    uint32_t pixels = (uint32_t)pixel_count;
    VkDeviceSize bytes = (VkDeviceSize)pixels * 4;
    uint64_t active_pixels = pixel_count / 10000 * active_basis_points +
        (pixel_count % 10000) * active_basis_points / 10000;
    if (active_pixels == 0) active_pixels = 1;
    VkDeviceSize active_bytes = (VkDeviceSize)active_pixels * 4;
    VkBufferCreateInfo bci = { .sType = 12, .size = bytes, .usage = 0x82 };
    VkBuffer buf = NULL;
    res = f_cb(dev, &bci, NULL, &buf);
    if (res) { printf("FAIL: vkCreateBuffer = %u\n", res); return 1; }

    VkMemoryRequirements mreq;
    f_gmr(dev, buf, &mreq);

    VkPhysicalDeviceMemoryProperties mprops;
    f_gmp(phys, &mprops);
    int32_t mt = find_mem_type(&mprops, mreq.memoryTypeBits, 0x02 | 0x04);
    if (mt < 0) { printf("FAIL: no host-visible memory\n"); return 1; }
    printf("  Memory type: %d (host-visible)\n", mt);

    VkMemoryAllocateInfo mai = { .sType = 5, .allocationSize = mreq.size, .memoryTypeIndex = (uint32_t)mt };
    VkDeviceMemory mem = NULL;
    res = f_am(dev, &mai, NULL, &mem);
    if (res) { printf("FAIL: vkAllocateMemory = %u\n", res); return 1; }
    res = f_bbm(dev, buf, mem, 0);
    if (res) { printf("FAIL: vkBindBufferMemory = %u\n", res); return 1; }
    printf("  Buffer: %llu bytes allocated + bound\n", (unsigned long long)bytes);

    /* --- Command pool + buffer + fence --- */
    VkCommandPoolCreateInfo cpci = { .sType = 39, .flags = 2, .queueFamilyIndex = 0 };
    VkCommandPool pool = NULL;
    res = f_ccp(dev, &cpci, NULL, &pool);
    if (res) { printf("FAIL: vkCreateCommandPool = %u\n", res); return 1; }

    VkCommandBufferAllocateInfo cbai = { .sType = 40, .commandPool = pool, .level = 0, .commandBufferCount = 1 };
    VkCommandBuffer cmd = NULL;
    res = f_acb(dev, &cbai, &cmd);
    if (res) { printf("FAIL: vkAllocateCommandBuffers = %u\n", res); return 1; }

    VkFenceCreateInfo fci = { .sType = 8 };
    VkFence fence = NULL;
    res = f_cf(dev, &fci, NULL, &fence);
    if (res) { printf("FAIL: vkCreateFence = %u\n", res); return 1; }
    printf("  Command pool + fence: OK\n");

    /* --- Record: vkCmdFillBuffer --- */
    VkCommandBufferBeginInfo cbbi = { .sType = 42 };
    res = f_bcb(cmd, &cbbi);
    if (res) { printf("FAIL: vkBeginCommandBuffer = %u\n", res); return 1; }
    f_cfb(cmd, buf, 0, active_bytes, 0xFF);
    res = f_ecb(cmd);
    if (res) { printf("FAIL: vkEndCommandBuffer = %u\n", res); return 1; }

    VkSubmitInfo si = { .sType = 4, .commandBufferCount = 1, .pCommandBuffers = &cmd };
    uint64_t timeout = 10000000000ULL;

    /* Warmup */
    res = f_qs(queue, 1, &si, fence);
    if (!res) res = f_wf(dev, 1, &fence, 1, timeout);
    if (!res) res = f_rf(dev, 1, &fence);
    if (res) { printf("FAIL: Vulkan warmup = %u\n", res); return 1; }

    /* --- Timed fill (each sample includes queue submit + fence wait/reset) --- */
    printf("\n--- GPU vkCmdFillBuffer %ux%u (%u iterations) ---\n", width, height, iterations);
    uint64_t* samples = calloc(iterations, sizeof(uint64_t));
    if (!samples) { printf("FAIL: timing allocation\n"); return 1; }
    t0 = now_ns();
    for (uint32_t i = 0; i < iterations; i++) {
        long long sample_start = now_ns();
        res = f_qs(queue, 1, &si, fence);
        if (!res) res = f_wf(dev, 1, &fence, 1, timeout);
        if (!res) res = f_rf(dev, 1, &fence);
        if (res) { printf("FAIL: Vulkan timed fill = %u\n", res); return 1; }
        samples[i] = (uint64_t)(now_ns() - sample_start);
    }
    long long gpu_ns = now_ns() - t0;
    qsort(samples, iterations, sizeof(uint64_t), compare_u64);
    uint64_t gpu_p50_ns = samples[(iterations - 1) / 2];
    uint32_t p95_index = (95 * iterations + 99) / 100 - 1;
    if (p95_index >= iterations) p95_index = iterations - 1;
    uint64_t gpu_p95_ns = samples[p95_index];
    printf("  Total: %.3f ms\n", (double)gpu_ns / 1000000.0);
    printf("  Avg:   %.3f ms/frame\n", (double)gpu_ns / (double)iterations / 1000000.0);
    printf("  p50:   %.3f ms/frame\n", (double)gpu_p50_ns / 1000000.0);
    printf("  p95:   %.3f ms/frame\n", (double)gpu_p95_ns / 1000000.0);

    /* --- Readback --- */
    printf("\n--- Readback ---\n");
    void* mapped = NULL;
    unsigned char* host = malloc((size_t)bytes);
    if (!host) { printf("  FAIL: host readback allocation\n"); return 1; }
    t0 = now_ns();
    res = f_mm(dev, mem, 0, bytes, 0, &mapped);
    if (!res) {
        measured_memcpy(host, mapped, (size_t)bytes);
        f_um(dev, mem);
    } else {
        printf("  FAIL: vkMapMemory = %u\n", res);
        return 1;
    }
    long long rb_ns = now_ns() - t0;
    uint32_t px0;
    memcpy(&px0, host, sizeof(px0));
    uint64_t active_checksum = 1469598103934665603ULL;
    uint64_t active_mismatch_count = 0;
    for (uint64_t i = 0; i < (uint64_t)active_bytes; i++) {
        active_checksum ^= host[i];
        active_checksum *= 1099511628211ULL;
    }
    for (uint64_t i = 0; i < active_pixels; i++) {
        uint32_t pixel;
        memcpy(&pixel, host + i * 4, sizeof(pixel));
        if (pixel != 0x000000FFu) active_mismatch_count++;
    }
    printf("  First pixel (u32): %u\n", px0);
    printf("  Full mapped readback: %.3f ms\n", (double)rb_ns / 1000000.0);

    /* --- CPU baseline --- */
    printf("\n--- CPU memset comparison (100 iterations) ---\n");
    unsigned char* cpu_buf = malloc((size_t)active_bytes);
    t0 = now_ns();
    for (uint32_t i = 0; i < iterations; i++)
        measured_memset(cpu_buf, 0x1E, (size_t)active_bytes);
    long long cpu_ns = now_ns() - t0;
    printf("  Total: %.3f ms\n", (double)cpu_ns / 1000000.0);
    printf("  Avg:   %.3f ms/frame\n", (double)cpu_ns / 100000000.0);
    free(cpu_buf);
    free(host);
    free(samples);

    /* --- Cleanup --- */
    if (f_dwi) f_dwi(dev);
    f_df(dev, fence, NULL);
    f_dcp(dev, pool, NULL);
    f_fm(dev, mem, NULL);
    f_db(dev, buf, NULL);
    f_dd(dev, NULL);
    f_di(instance, NULL);
    dlclose(lib);

    /* --- Verdict --- */
    printf("\n========================================\n");
    printf("VULKAN VERDICT\n");
    printf("========================================\n");
    printf("vulkan_8k_schema=vulkan-buffer-fill-v2\n");
    printf("vulkan_8k_width=%u\n", width);
    printf("vulkan_8k_height=%u\n", height);
    printf("vulkan_8k_pixels=%u\n", pixels);
    printf("vulkan_8k_active_pixels=%llu\n", (unsigned long long)active_pixels);
    printf("vulkan_8k_active_basis_points=%u\n", active_basis_points);
    printf("vulkan_8k_active_bytes=%llu\n", (unsigned long long)active_bytes);
    printf("vulkan_8k_iterations=%u\n", iterations);
    printf("vulkan_8k_device_name=%s\n", selected_device_name);
    printf("vulkan_8k_device_type_code=%u\n", selected_device_type);
    printf("vulkan_8k_physical_gpu=%s\n", selected_device_type == 1 || selected_device_type == 2 ? "true" : "false");
    printf("vulkan_8k_submit_fence_p50_ns=%llu\n", (unsigned long long)gpu_p50_ns);
    printf("vulkan_8k_submit_fence_p95_ns=%llu\n", (unsigned long long)gpu_p95_ns);
    printf("vulkan_8k_submit_fence_within_80fps_budget=%s\n", gpu_p95_ns <= 12500000ULL ? "true" : "false");
    printf("vulkan_8k_timed_readback_bytes=0\n");
    printf("vulkan_8k_evidence_readback_bytes=%llu\n", (unsigned long long)bytes);
    printf("vulkan_8k_active_checksum=%llu\n", (unsigned long long)active_checksum);
    printf("vulkan_8k_active_mismatch_count=%llu\n", (unsigned long long)active_mismatch_count);
    printf("vulkan_8k_swapchain_presented=false\n");
    printf("vulkan_8k_dynamic_frame_80fps_proven=false\n");
    printf("  Vulkan available: YES (%u devices)\n", dev_count);
    printf("  Init time: %.3f ms (target < 500 ms)\n", init_ms);
    if (init_ms < 500) printf("  PASS: init within NFR target\n");
    else printf("  WARN: init exceeds 500ms target\n");
    printf("  GPU fill avg: %.2f ms\n", (double)gpu_ns / (double)iterations / 1000000.0);
    printf("  CPU memset avg: %.2f ms\n", (double)cpu_ns / (double)iterations / 1000000.0);
    printf("  GPU fill + full mapped readback: %.2f ms\n",
        (double)gpu_ns / (double)iterations / 1000000.0 + (double)rb_ns / 1000000.0);
    if (gpu_ns > 0 && cpu_ns > gpu_ns) printf("  GPU speedup: %.1fx\n", (double)cpu_ns / gpu_ns);
    if (gpu_ns > 0 && gpu_ns >= cpu_ns) printf("  NOTE: host-visible mem slower than CPU (expected on discrete GPU)\n");
    if (offload_preferred(cpu_ns, gpu_ns)) printf("  Fill offload: preferred\n");
    else printf("  Fill offload: available-not-preferred\n");
    if (offload_preferred(cpu_ns, gpu_ns + rb_ns * iterations)) printf("  Roundtrip offload: preferred\n");
    else printf("  Roundtrip offload: available-not-preferred (communication overhead)\n");
    if ((double)gpu_ns / (double)iterations / 1000000.0 < 16.7) printf("  PASS: GPU < 16.7ms/frame -> 60Hz capable\n");
    else printf("  WARN: GPU > 16.7ms/frame\n");
    printf("========================================\n");
    return 0;
}
