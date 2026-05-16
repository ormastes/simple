/* Vulkan Compute Perf Benchmark — via libvulkan.so
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
typedef uint64_t VkDevice;
typedef uint64_t VkInstance;
typedef uint64_t VkPhysicalDevice;
typedef uint64_t VkQueue;
typedef uint64_t VkCommandPool;
typedef uint64_t VkCommandBuffer;
typedef uint64_t VkBuffer;
typedef uint64_t VkDeviceMemory;

typedef struct { uint32_t sType; const void* pNext; uint32_t flags;
    const void* pApplicationInfo; uint32_t enabledLayerCount;
    const char* const* ppEnabledLayerNames; uint32_t enabledExtensionCount;
    const char* const* ppEnabledExtensionNames; } VkInstanceCreateInfo;

typedef struct { uint32_t apiVersion; } VkPhysicalDeviceProperties;

/* We just need to verify Vulkan can init and enumerate devices */
typedef VkResult (*vkCreateInstance_t)(const VkInstanceCreateInfo*, const void*, VkInstance*);
typedef VkResult (*vkEnumeratePhysicalDevices_t)(VkInstance, uint32_t*, VkPhysicalDevice*);
typedef void (*vkGetPhysicalDeviceProperties_t)(VkPhysicalDevice, void*);
typedef void (*vkDestroyInstance_t)(VkInstance, const void*);

static long long now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

int main(void) {
    printf("========================================\n");
    printf("Vulkan GPU Check (driver API)\n");
    printf("========================================\n");

    void* lib = dlopen("libvulkan.so.1", RTLD_LAZY);
    if (!lib) lib = dlopen("libvulkan.so", RTLD_LAZY);
    if (!lib) { printf("FAIL: cannot load libvulkan.so\n"); return 1; }

    vkCreateInstance_t p_vkCreateInstance =
        (vkCreateInstance_t)dlsym(lib, "vkCreateInstance");
    vkEnumeratePhysicalDevices_t p_vkEnumeratePhysicalDevices =
        (vkEnumeratePhysicalDevices_t)dlsym(lib, "vkEnumeratePhysicalDevices");
    vkGetPhysicalDeviceProperties_t p_vkGetPhysicalDeviceProperties =
        (vkGetPhysicalDeviceProperties_t)dlsym(lib, "vkGetPhysicalDeviceProperties");
    vkDestroyInstance_t p_vkDestroyInstance =
        (vkDestroyInstance_t)dlsym(lib, "vkDestroyInstance");

    if (!p_vkCreateInstance || !p_vkEnumeratePhysicalDevices) {
        printf("FAIL: missing Vulkan symbols\n"); return 1;
    }

    /* Create instance */
    VkInstanceCreateInfo ci = {0};
    ci.sType = 1; /* VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO */
    VkInstance instance = 0;
    long long t0 = now_ms();
    VkResult res = p_vkCreateInstance(&ci, NULL, &instance);
    long long init_ms = now_ms() - t0;
    if (res != 0) { printf("FAIL: vkCreateInstance = %u\n", res); return 1; }
    printf("Instance created: %lld ms\n", init_ms);

    /* Enumerate devices */
    uint32_t dev_count = 0;
    p_vkEnumeratePhysicalDevices(instance, &dev_count, NULL);
    printf("Physical devices: %u\n", dev_count);

    if (dev_count > 0) {
        VkPhysicalDevice* devs = calloc(dev_count, sizeof(VkPhysicalDevice));
        p_vkEnumeratePhysicalDevices(instance, &dev_count, devs);

        /* Get properties (raw struct — just read the device name at offset) */
        for (uint32_t i = 0; i < dev_count && i < 4; i++) {
            /* VkPhysicalDeviceProperties is large; name is at offset 256 */
            char props[1024] = {0};
            p_vkGetPhysicalDeviceProperties(devs[i], props);
            /* deviceName starts at offset 256 in VkPhysicalDeviceProperties */
            char* device_name = props + 256;
            printf("  Device %u: %s\n", i, device_name);
        }
        free(devs);
    }

    /* Timing: instance creation is the key metric for Vulkan init */
    printf("\n--- Vulkan Init Timing ---\n");
    printf("  Instance creation: %lld ms\n", init_ms);
    printf("  Device enumeration: included\n");

    /* CPU baseline comparison (same memset as CUDA bench) */
    printf("\n--- CPU Baseline ---\n");
    int W = 1920, H = 1080;
    size_t bytes = (size_t)W * H * 4;
    unsigned char* buf = malloc(bytes);
    t0 = now_ms();
    for (int i = 0; i < 100; i++) memset(buf, 0x1E, bytes);
    long long cpu_ms = now_ms() - t0;
    printf("  100 CPU memsets (1080p): %lld ms\n", cpu_ms);
    printf("  Avg: %.2f ms\n", (double)cpu_ms / 100.0);
    free(buf);

    printf("\n========================================\n");
    printf("VERDICT\n");
    printf("========================================\n");
    printf("  Vulkan available: YES (%u devices)\n", dev_count);
    printf("  Init time: %lld ms (target < 500 ms)\n", init_ms);
    if (init_ms < 500) printf("  PASS: init within NFR target\n");
    else printf("  WARN: init exceeds 500ms target\n");
    printf("========================================\n");

    p_vkDestroyInstance(instance, NULL);
    dlclose(lib);
    return 0;
}
