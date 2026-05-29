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

static long long now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static int32_t find_mem_type(const VkPhysicalDeviceMemoryProperties* p, uint32_t bits, VkFlags flags) {
    for (uint32_t i = 0; i < p->memoryTypeCount; i++)
        if ((bits & (1u << i)) && (p->memoryTypes[i].propertyFlags & flags) == flags)
            return (int32_t)i;
    return -1;
}

int main(void) {
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
    long long t0 = now_ms();
    VkResult res = f_ci(&ici, NULL, &instance);
    long long init_ms = now_ms() - t0;
    if (res) { printf("FAIL: vkCreateInstance = %u\n", res); return 1; }
    printf("  Instance created: %lld ms\n", init_ms);

    /* --- Enumerate --- */
    uint32_t dev_count = 0;
    f_epd(instance, &dev_count, NULL);
    printf("  Physical devices: %u\n", dev_count);
    if (!dev_count) { printf("FAIL: no devices\n"); return 1; }

    VkPhysicalDevice* devs = calloc(dev_count, sizeof(VkPhysicalDevice));
    f_epd(instance, &dev_count, devs);
    VkPhysicalDevice phys = devs[0];

    if (f_gpp) {
        for (uint32_t i = 0; i < dev_count && i < 4; i++) {
            char props[1024] = {0};
            f_gpp(devs[i], props);
            printf("    Device %u: %s\n", i, props + 20);
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

    /* --- Buffer (1080p, storage+transfer_dst) --- */
    uint32_t pixels = 1920 * 1080;
    VkDeviceSize bytes = (VkDeviceSize)pixels * 4;
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
    f_bcb(cmd, &cbbi);
    f_cfb(cmd, buf, 0, bytes, 0xFF);
    f_ecb(cmd);

    VkSubmitInfo si = { .sType = 4, .commandBufferCount = 1, .pCommandBuffers = &cmd };
    uint64_t timeout = 10000000000ULL;

    /* Warmup */
    f_qs(queue, 1, &si, fence);
    f_wf(dev, 1, &fence, 1, timeout);
    f_rf(dev, 1, &fence);

    /* --- Timed fill (100 iterations) --- */
    printf("\n--- GPU vkCmdFillBuffer 1080p (100 iterations) ---\n");
    t0 = now_ms();
    for (int i = 0; i < 100; i++) {
        f_qs(queue, 1, &si, fence);
        f_wf(dev, 1, &fence, 1, timeout);
        f_rf(dev, 1, &fence);
    }
    long long gpu_ms = now_ms() - t0;
    printf("  Total: %lld ms\n", gpu_ms);
    printf("  Avg:   %.2f ms/frame\n", (double)gpu_ms / 100.0);

    /* --- Readback --- */
    printf("\n--- Readback ---\n");
    void* mapped = NULL;
    res = f_mm(dev, mem, 0, bytes, 0, &mapped);
    if (!res) {
        uint32_t px0 = *(uint32_t*)mapped;
        printf("  First pixel (u32): %u\n", px0);
        f_um(dev, mem);
    } else {
        printf("  WARN: vkMapMemory failed = %u\n", res);
    }

    /* --- CPU baseline --- */
    printf("\n--- CPU memset comparison (100 iterations) ---\n");
    unsigned char* cpu_buf = malloc(bytes);
    t0 = now_ms();
    for (int i = 0; i < 100; i++) memset(cpu_buf, 0x1E, bytes);
    long long cpu_ms = now_ms() - t0;
    printf("  Total: %lld ms\n", cpu_ms);
    printf("  Avg:   %.2f ms/frame\n", (double)cpu_ms / 100.0);
    free(cpu_buf);

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
    printf("  Vulkan available: YES (%u devices)\n", dev_count);
    printf("  Init time: %lld ms (target < 500 ms)\n", init_ms);
    if (init_ms < 500) printf("  PASS: init within NFR target\n");
    else printf("  WARN: init exceeds 500ms target\n");
    printf("  GPU fill avg: %.2f ms\n", (double)gpu_ms / 100.0);
    printf("  CPU memset avg: %.2f ms\n", (double)cpu_ms / 100.0);
    if (gpu_ms > 0 && cpu_ms > gpu_ms) printf("  GPU speedup: %lldx\n", cpu_ms / gpu_ms);
    if (gpu_ms > 0 && gpu_ms >= cpu_ms) printf("  NOTE: host-visible mem slower than CPU (expected on discrete GPU)\n");
    if (gpu_ms / 100 < 17) printf("  PASS: GPU < 16.7ms/frame -> 60Hz capable\n");
    else printf("  WARN: GPU > 16.7ms/frame\n");
    printf("========================================\n");
    return 0;
}
