#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <signal.h>
#include <unistd.h>
#include <link.h>
#include <elf.h>
#include <vulkan/vulkan.h>
#include <renderdoc_app.h>

static RENDERDOC_API_1_6_0 *rdoc_api;
static PFN_vkQueuePresentKHR real_vkQueuePresentKHR;
static PFN_vkQueueSubmit real_vkQueueSubmit;
static PFN_vkQueueSubmit2 real_vkQueueSubmit2;
static PFN_vkQueueSubmit2KHR real_vkQueueSubmit2KHR;
static PFN_vkCreateInstance real_vkCreateInstance;
static PFN_vkCreateDevice real_vkCreateDevice;
static PFN_vkEnumeratePhysicalDevices real_vkEnumeratePhysicalDevices;
static PFN_vkGetPhysicalDeviceProperties real_vkGetPhysicalDeviceProperties;
static PFN_vkGetPhysicalDeviceProperties2 real_vkGetPhysicalDeviceProperties2;
static PFN_vkGetPhysicalDeviceProperties2KHR real_vkGetPhysicalDeviceProperties2KHR;
static PFN_vkGetPhysicalDeviceFeatures2 real_vkGetPhysicalDeviceFeatures2;
static PFN_vkGetPhysicalDeviceFeatures2KHR real_vkGetPhysicalDeviceFeatures2KHR;
static PFN_vkGetPhysicalDeviceQueueFamilyProperties real_vkGetPhysicalDeviceQueueFamilyProperties;
static PFN_vkGetPhysicalDeviceQueueFamilyProperties2 real_vkGetPhysicalDeviceQueueFamilyProperties2;
static PFN_vkGetPhysicalDeviceQueueFamilyProperties2KHR real_vkGetPhysicalDeviceQueueFamilyProperties2KHR;
static PFN_vkEnumerateDeviceExtensionProperties real_vkEnumerateDeviceExtensionProperties;
static PFN_vkEnumerateInstanceLayerProperties real_vkEnumerateInstanceLayerProperties;
static PFN_vkEnumerateInstanceExtensionProperties real_vkEnumerateInstanceExtensionProperties;
static PFN_vkEnumerateInstanceVersion real_vkEnumerateInstanceVersion;
static PFN_vkGetDeviceProcAddr real_vkGetDeviceProcAddr;
static PFN_vkGetInstanceProcAddr real_vkGetInstanceProcAddr;
typedef int (*egl_swap_buffers_fn_t)(void *, void *);
typedef void *(*egl_get_proc_address_fn_t)(const char *);
typedef void (*egl_vulkan_queue_lock_fn_t)(void *);
typedef int (*egl_display_surface_fn_t)(void *, void *);
typedef int (*egl_display_fn_t)(void *);
typedef int (*egl_make_current_fn_t)(void *, void *, void *, void *);
typedef void *(*egl_create_window_surface_fn_t)(void *, void *, void *, const void *);
typedef void *(*egl_get_display_fn_t)(void *);
typedef void *(*egl_get_platform_display_fn_t)(unsigned int, void *, const void *);
typedef int (*egl_initialize_fn_t)(void *, int *, int *);
typedef int (*egl_choose_config_fn_t)(void *, const int *, void *, int, int *);
typedef int (*egl_get_error_fn_t)(void);
static egl_swap_buffers_fn_t real_eglSwapBuffers;
static egl_get_proc_address_fn_t real_eglGetProcAddress;
static egl_vulkan_queue_lock_fn_t real_eglLockVulkanQueueANGLE;
static egl_vulkan_queue_lock_fn_t real_eglUnlockVulkanQueueANGLE;
static egl_display_surface_fn_t real_eglPrepareSwapBuffersANGLE;
static egl_display_fn_t real_eglWaitUntilWorkScheduledANGLE;
static egl_make_current_fn_t real_eglMakeCurrent;
static egl_create_window_surface_fn_t real_eglCreateWindowSurface;
static egl_create_window_surface_fn_t real_eglCreatePlatformWindowSurface;
static egl_get_display_fn_t real_eglGetDisplay;
static egl_get_platform_display_fn_t real_eglGetPlatformDisplay;
static egl_initialize_fn_t real_eglInitialize;
static egl_choose_config_fn_t real_eglChooseConfig;
static egl_get_error_fn_t real_eglGetError;
typedef void *(*real_dlsym_fn_t)(void *, const char *);
static real_dlsym_fn_t real_dlsym_fn;
static void *real_vulkan_handle;
static void *real_egl_handle;
static int capture_started;
static int capture_finished;
static int delay_thread_started;
static int summary_thread_started;
static const char *capture_start_source;
static const char *capture_end_source;
static uint64_t submit_count;
static uint64_t present_count;
static uint64_t egl_swap_count;
static uint64_t egl_vulkan_queue_lock_count;
static uint64_t egl_vulkan_queue_unlock_count;
static uint64_t egl_prepare_swap_count;
static uint64_t egl_wait_scheduled_count;
static uint64_t egl_make_current_count;
static uint64_t egl_create_window_surface_count;
static uint64_t egl_create_platform_window_surface_count;
static uint64_t egl_get_display_count;
static uint64_t egl_get_platform_display_count;
static uint64_t egl_initialize_count;
static uint64_t egl_initialize_return_count;
static uint64_t egl_initialize_success_count;
static uint64_t egl_initialize_fail_count;
static int egl_initialize_last_result = -1;
static int egl_initialize_last_error = -1;
static uint64_t egl_choose_config_count;
static uint64_t vk_create_instance_count;
static uint64_t vk_create_device_count;
static uint64_t vk_enum_physical_device_count;
static uint64_t vk_enum_physical_device_return_count;
static int vk_enum_physical_device_last_result = 0;
static uint32_t vk_enum_physical_device_last_count;
static uint64_t vk_get_physical_device_properties_count;
static uint64_t vk_get_physical_device_properties2_count;
static uint64_t vk_get_physical_device_features2_count;
static uint64_t vk_get_physical_device_queue_family_count;
static uint64_t vk_get_physical_device_queue_family2_count;
static uint32_t vk_get_physical_device_queue_family_last_count;
static uint32_t vk_get_physical_device_queue_family2_last_count;
static uint64_t vk_enum_device_extension_count;
static uint64_t vk_enum_device_extension_return_count;
static int vk_enum_device_extension_last_result = 0;
static uint32_t vk_enum_device_extension_last_count;
static uint64_t vk_enum_instance_layer_count;
static uint64_t vk_enum_instance_extension_count;
static uint64_t proc_trace_count;
static uint64_t gipa_trace_count;
static uint64_t gdpa_trace_count;

static int env_enabled(const char *name);
static uint64_t env_u64(const char *name, uint64_t fallback);
static void hex_bytes(char *out, size_t out_size, const uint8_t *bytes, size_t byte_count);
static uintptr_t find_loaded_symbol_no_loader_lock(const char *library_hint, const char *symbol);
static int is_egl_intercept_symbol(const char *name);
void eglLockVulkanQueueANGLE(void *display);
void eglUnlockVulkanQueueANGLE(void *display);
int eglPrepareSwapBuffersANGLE(void *display, void *surface);
int eglWaitUntilWorkScheduledANGLE(void *display);
int eglMakeCurrent(void *display, void *draw, void *read, void *context);
void *eglCreateWindowSurface(void *display, void *config, void *native_window, const void *attrib_list);
void *eglCreatePlatformWindowSurface(void *display, void *config, void *native_window, const void *attrib_list);
void *eglGetDisplay(void *native_display);
void *eglGetPlatformDisplay(unsigned int platform, void *native_display, const void *attrib_list);
int eglInitialize(void *display, int *major, int *minor);
int eglChooseConfig(void *display, const int *attrib_list, void *configs, int config_size, int *num_config);
int eglGetError(void);
VKAPI_ATTR VkResult VKAPI_CALL vkCreateInstance(const VkInstanceCreateInfo *pCreateInfo, const VkAllocationCallbacks *pAllocator, VkInstance *pInstance);
VKAPI_ATTR VkResult VKAPI_CALL vkCreateDevice(VkPhysicalDevice physicalDevice, const VkDeviceCreateInfo *pCreateInfo, const VkAllocationCallbacks *pAllocator, VkDevice *pDevice);
VKAPI_ATTR VkResult VKAPI_CALL vkEnumeratePhysicalDevices(VkInstance instance, uint32_t *pPhysicalDeviceCount, VkPhysicalDevice *pPhysicalDevices);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceProperties(VkPhysicalDevice physicalDevice, VkPhysicalDeviceProperties *pProperties);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceProperties2(VkPhysicalDevice physicalDevice, VkPhysicalDeviceProperties2 *pProperties);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceProperties2KHR(VkPhysicalDevice physicalDevice, VkPhysicalDeviceProperties2 *pProperties);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceFeatures2(VkPhysicalDevice physicalDevice, VkPhysicalDeviceFeatures2 *pFeatures);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceFeatures2KHR(VkPhysicalDevice physicalDevice, VkPhysicalDeviceFeatures2 *pFeatures);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceQueueFamilyProperties(VkPhysicalDevice physicalDevice, uint32_t *pQueueFamilyPropertyCount, VkQueueFamilyProperties *pQueueFamilyProperties);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceQueueFamilyProperties2(VkPhysicalDevice physicalDevice, uint32_t *pQueueFamilyPropertyCount, VkQueueFamilyProperties2 *pQueueFamilyProperties);
VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceQueueFamilyProperties2KHR(VkPhysicalDevice physicalDevice, uint32_t *pQueueFamilyPropertyCount, VkQueueFamilyProperties2 *pQueueFamilyProperties);
VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateDeviceExtensionProperties(VkPhysicalDevice physicalDevice, const char *pLayerName, uint32_t *pPropertyCount, VkExtensionProperties *pProperties);
VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateInstanceLayerProperties(uint32_t *pPropertyCount, VkLayerProperties *pProperties);
VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateInstanceExtensionProperties(const char *pLayerName, uint32_t *pPropertyCount, VkExtensionProperties *pProperties);
VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateInstanceVersion(uint32_t *pApiVersion);

struct library_lookup {
    const char *needle;
    uintptr_t base;
    char path[1024];
};

static void log_line(const char *msg) {
    const char *path = getenv("RDOC_AUTOCAPTURE_LOG");
    if (!path || !*path) return;
    FILE *f = fopen(path, "a");
    if (!f) return;
    fprintf(f, "%s\n", msg);
    fclose(f);
}

static void trace_proc_name(const char *source, const char *name) {
    if (!env_enabled("RDOC_AUTOCAPTURE_TRACE_PROC_NAMES")) return;
    uint64_t max = env_u64("RDOC_AUTOCAPTURE_TRACE_PROC_NAMES_MAX", 200);
    if (proc_trace_count >= max) return;
    proc_trace_count++;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_proc_%s=%s", source, name ? name : "(null)");
    log_line(buf);
}

static void trace_vulkan_proc_name(const char *source, const char *name) {
    if (!env_enabled("RDOC_AUTOCAPTURE_TRACE_PROC_NAMES")) return;
    uint64_t max = env_u64("RDOC_AUTOCAPTURE_TRACE_VK_PROC_NAMES_MAX", 160);
    uint64_t *count = strcmp(source, "gdpa") == 0 ? &gdpa_trace_count : &gipa_trace_count;
    if (*count >= max) return;
    (*count)++;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_vkproc_%s=%s", source, name ? name : "(null)");
    log_line(buf);
}

static void trace_vulkan_proc_result(const char *source, const char *name, PFN_vkVoidFunction result) {
    if (!env_enabled("RDOC_AUTOCAPTURE_TRACE_PROC_NAMES")) return;
    char buf[320];
    snprintf(buf, sizeof(buf),
        "rdoc_autocapture_vkproc_%s_result=%s found:%u",
        source,
        name ? name : "(null)",
        result ? 1U : 0U);
    log_line(buf);
}

static void sanitize_log_value(char *text) {
    if (!text) return;
    for (char *p = text; *p; p++) {
        if (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') *p = '_';
    }
}

static void log_physical_device_properties2(const VkPhysicalDeviceProperties2 *props) {
    if (!props) return;
    char name[VK_MAX_PHYSICAL_DEVICE_NAME_SIZE];
    snprintf(name, sizeof(name), "%s", props->properties.deviceName);
    sanitize_log_value(name);
    char buf[768];
    snprintf(buf, sizeof(buf),
        "rdoc_autocapture_physical_device_properties2=index:%llu type:%u vendor:%u device:%u api:%u driver:%u name:%s",
        (unsigned long long)vk_get_physical_device_properties2_count,
        (unsigned int)props->properties.deviceType,
        (unsigned int)props->properties.vendorID,
        (unsigned int)props->properties.deviceID,
        (unsigned int)props->properties.apiVersion,
        (unsigned int)props->properties.driverVersion,
        name);
    log_line(buf);

    const VkBaseOutStructure *node = (const VkBaseOutStructure *)props->pNext;
    unsigned int depth = 0;
    while (node && depth < 16) {
        snprintf(buf, sizeof(buf),
            "rdoc_autocapture_physical_device_properties2_pnext=index:%llu depth:%u stype:%u",
            (unsigned long long)vk_get_physical_device_properties2_count,
            depth,
            (unsigned int)node->sType);
        log_line(buf);
        if (node->sType == VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_DRIVER_PROPERTIES) {
            const VkPhysicalDeviceDriverProperties *driver = (const VkPhysicalDeviceDriverProperties *)node;
            char driver_name[VK_MAX_DRIVER_NAME_SIZE];
            char driver_info[VK_MAX_DRIVER_INFO_SIZE];
            snprintf(driver_name, sizeof(driver_name), "%s", driver->driverName);
            snprintf(driver_info, sizeof(driver_info), "%s", driver->driverInfo);
            sanitize_log_value(driver_name);
            sanitize_log_value(driver_info);
            snprintf(buf, sizeof(buf),
                "rdoc_autocapture_physical_device_driver_properties=index:%llu driver_id:%u name:%s info:%s conformance:%u.%u.%u.%u",
                (unsigned long long)vk_get_physical_device_properties2_count,
                (unsigned int)driver->driverID,
                driver_name,
                driver_info,
                (unsigned int)driver->conformanceVersion.major,
                (unsigned int)driver->conformanceVersion.minor,
                (unsigned int)driver->conformanceVersion.subminor,
                (unsigned int)driver->conformanceVersion.patch);
            log_line(buf);
        } else if (node->sType == VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_ID_PROPERTIES) {
            const VkPhysicalDeviceIDProperties *id = (const VkPhysicalDeviceIDProperties *)node;
            char device_uuid[VK_UUID_SIZE * 2 + 1];
            char driver_uuid[VK_UUID_SIZE * 2 + 1];
            char device_luid[VK_LUID_SIZE * 2 + 1];
            hex_bytes(device_uuid, sizeof(device_uuid), id->deviceUUID, VK_UUID_SIZE);
            hex_bytes(driver_uuid, sizeof(driver_uuid), id->driverUUID, VK_UUID_SIZE);
            hex_bytes(device_luid, sizeof(device_luid), id->deviceLUID, VK_LUID_SIZE);
            snprintf(buf, sizeof(buf),
                "rdoc_autocapture_physical_device_id_properties=index:%llu device_uuid:%s driver_uuid:%s luid:%s node_mask:%u luid_valid:%u",
                (unsigned long long)vk_get_physical_device_properties2_count,
                device_uuid,
                driver_uuid,
                device_luid,
                (unsigned int)id->deviceNodeMask,
                (unsigned int)id->deviceLUIDValid);
            log_line(buf);
        } else if (node->sType == VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_VULKAN_1_2_PROPERTIES) {
            const VkPhysicalDeviceVulkan12Properties *v12 = (const VkPhysicalDeviceVulkan12Properties *)node;
            char driver_name[VK_MAX_DRIVER_NAME_SIZE];
            char driver_info[VK_MAX_DRIVER_INFO_SIZE];
            snprintf(driver_name, sizeof(driver_name), "%s", v12->driverName);
            snprintf(driver_info, sizeof(driver_info), "%s", v12->driverInfo);
            sanitize_log_value(driver_name);
            sanitize_log_value(driver_info);
            snprintf(buf, sizeof(buf),
                "rdoc_autocapture_physical_device_vulkan12_properties=index:%llu driver_id:%u name:%s info:%s conformance:%u.%u.%u.%u",
                (unsigned long long)vk_get_physical_device_properties2_count,
                (unsigned int)v12->driverID,
                driver_name,
                driver_info,
                (unsigned int)v12->conformanceVersion.major,
                (unsigned int)v12->conformanceVersion.minor,
                (unsigned int)v12->conformanceVersion.subminor,
                (unsigned int)v12->conformanceVersion.patch);
            log_line(buf);
        }
        node = node->pNext;
        depth++;
    }
}

static void log_extension_properties(
    const char *kind,
    uint64_t call_index,
    const char *layer_name,
    VkResult result,
    const uint32_t *count,
    const VkExtensionProperties *props) {
    char layer[128];
    snprintf(layer, sizeof(layer), "%s", layer_name ? layer_name : "(null)");
    sanitize_log_value(layer);
    char buf[512];
    snprintf(buf, sizeof(buf),
        "rdoc_autocapture_%s_extensions=index:%llu result:%d count:%u layer:%s populated:%u",
        kind,
        (unsigned long long)call_index,
        (int)result,
        count ? (unsigned int)*count : 0,
        layer,
        props ? 1U : 0U);
    log_line(buf);
    if (!props || !count) return;
    uint32_t max = (uint32_t)env_u64("RDOC_AUTOCAPTURE_TRACE_EXTENSION_NAMES_MAX", 64);
    uint32_t limit = *count < max ? *count : max;
    for (uint32_t i = 0; i < limit; i++) {
        char name[VK_MAX_EXTENSION_NAME_SIZE];
        snprintf(name, sizeof(name), "%s", props[i].extensionName);
        sanitize_log_value(name);
        snprintf(buf, sizeof(buf),
            "rdoc_autocapture_%s_extension=index:%llu ordinal:%u spec:%u name:%s",
            kind,
            (unsigned long long)call_index,
            (unsigned int)i,
            (unsigned int)props[i].specVersion,
            name);
        log_line(buf);
    }
}

static void hex_bytes(char *out, size_t out_size, const uint8_t *bytes, size_t byte_count) {
    static const char hex[] = "0123456789abcdef";
    if (!out || out_size == 0) return;
    size_t limit = byte_count;
    if (limit * 2 + 1 > out_size) limit = (out_size - 1) / 2;
    for (size_t i = 0; i < limit; i++) {
        out[i * 2] = hex[(bytes[i] >> 4) & 0xf];
        out[i * 2 + 1] = hex[bytes[i] & 0xf];
    }
    out[limit * 2] = '\0';
}

static void log_string_list(const char *kind, const char *const *names, uint32_t count) {
    char buf[512];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_%s_count=%u", kind, (unsigned int)count);
    log_line(buf);
    uint32_t max = (uint32_t)env_u64("RDOC_AUTOCAPTURE_TRACE_CREATE_INFO_NAMES_MAX", 64);
    uint32_t limit = count < max ? count : max;
    for (uint32_t i = 0; i < limit; i++) {
        char name[VK_MAX_EXTENSION_NAME_SIZE];
        snprintf(name, sizeof(name), "%s", names && names[i] ? names[i] : "(null)");
        sanitize_log_value(name);
        snprintf(buf, sizeof(buf),
            "rdoc_autocapture_%s=ordinal:%u name:%s",
            kind,
            (unsigned int)i,
            name);
        log_line(buf);
    }
}

static void *real_dlsym_lookup(void *handle, const char *symbol) {
    if (!real_dlsym_fn) {
        real_dlsym_fn = (real_dlsym_fn_t)dlvsym(RTLD_NEXT, "dlsym", "GLIBC_2.2.5");
    }
    if (!real_dlsym_fn) return NULL;
    return real_dlsym_fn(handle, symbol);
}

static void *library_symbol(const char *library_name, void **cached_handle, const char *symbol) {
    if (!*cached_handle) {
        *cached_handle = dlopen(library_name, RTLD_NOW | RTLD_NOLOAD);
        if (!*cached_handle) *cached_handle = dlopen(library_name, RTLD_NOW | RTLD_LOCAL);
    }
    return *cached_handle ? real_dlsym_lookup(*cached_handle, symbol) : NULL;
}

static void *real_next_symbol(const char *symbol) {
    void *result = real_dlsym_lookup(RTLD_NEXT, symbol);
    if (result) return result;
    if (strncmp(symbol, "vk", 2) == 0) {
        result = library_symbol("libvulkan.so.1", &real_vulkan_handle, symbol);
        if (!result) result = library_symbol("libvulkan.so", &real_vulkan_handle, symbol);
        return result;
    }
    if (strncmp(symbol, "egl", 3) == 0 || strncmp(symbol, "EGL_", 4) == 0) {
        result = library_symbol("libEGL.so.1", &real_egl_handle, symbol);
        if (!result) result = library_symbol("libEGL.so", &real_egl_handle, symbol);
        return result;
    }
    return NULL;
}

static void load_renderdoc_api(void) {
    if (rdoc_api) return;
    log_line("rdoc_autocapture_api=loading");
    pRENDERDOC_GetAPI get_api = NULL;
    if (!env_enabled("RDOC_AUTOCAPTURE_ALLOW_DLOPEN")) {
        log_line("rdoc_autocapture_api=dlsym-default-start");
        get_api = (pRENDERDOC_GetAPI)real_dlsym_lookup(RTLD_DEFAULT, "RENDERDOC_GetAPI");
        log_line(get_api ? "rdoc_autocapture_api=dlsym-default-found" : "rdoc_autocapture_api=dlsym-default-missing");
    } else {
        log_line("rdoc_autocapture_api=dlsym-default-skipped");
    }
    if (!get_api && !env_enabled("RDOC_AUTOCAPTURE_ALLOW_DLOPEN")) {
        log_line("rdoc_autocapture_api=missing-symbol-default");
        return;
    }
    const char *libpath = getenv("RDOC_AUTOCAPTURE_RENDERDOC_LIB");
    void *handle = NULL;
    if (!get_api && env_enabled("RDOC_AUTOCAPTURE_ALLOW_DLOPEN")) {
        log_line("rdoc_autocapture_api=elf-lookup-start");
        get_api = (pRENDERDOC_GetAPI)find_loaded_symbol_no_loader_lock(libpath, "RENDERDOC_GetAPI");
        if (get_api) log_line("rdoc_autocapture_api=elf-lookup-found");
    }
    if (!get_api && env_enabled("RDOC_AUTOCAPTURE_ALLOW_DLOPEN") &&
        !env_enabled("RDOC_AUTOCAPTURE_NO_DLOPEN_FALLBACK")) {
        if (libpath && *libpath) {
            log_line("rdoc_autocapture_api=dlopen-noload-path-start");
            handle = dlopen(libpath, RTLD_NOW | RTLD_NOLOAD);
            log_line(handle ? "rdoc_autocapture_api=dlopen-noload-path-found" : "rdoc_autocapture_api=dlopen-noload-path-missing");
        }
        if (!handle) {
            log_line("rdoc_autocapture_api=dlopen-noload-name-start");
            handle = dlopen("librenderdoc.so", RTLD_NOW | RTLD_NOLOAD);
            log_line(handle ? "rdoc_autocapture_api=dlopen-noload-name-found" : "rdoc_autocapture_api=dlopen-noload-name-missing");
        }
        if (!handle && libpath && *libpath) {
            log_line("rdoc_autocapture_api=dlopen-path-start");
            handle = dlopen(libpath, RTLD_NOW | RTLD_LOCAL);
            log_line(handle ? "rdoc_autocapture_api=dlopen-path-found" : "rdoc_autocapture_api=dlopen-path-missing");
        }
        if (!handle) {
            log_line("rdoc_autocapture_api=dlopen-name-start");
            handle = dlopen("librenderdoc.so", RTLD_NOW | RTLD_LOCAL);
            log_line(handle ? "rdoc_autocapture_api=dlopen-name-found" : "rdoc_autocapture_api=dlopen-name-missing");
        }
    }
    if (!get_api && !handle) {
        log_line("rdoc_autocapture_api=missing-librenderdoc");
        return;
    }
    if (!get_api) {
        log_line("rdoc_autocapture_api=dlsym-handle-start");
        get_api = (pRENDERDOC_GetAPI)real_dlsym_lookup(handle, "RENDERDOC_GetAPI");
        log_line(get_api ? "rdoc_autocapture_api=dlsym-handle-found" : "rdoc_autocapture_api=dlsym-handle-missing");
    }
    if (!get_api) {
        log_line("rdoc_autocapture_api=missing-symbol");
        return;
    }
    if (!get_api(eRENDERDOC_API_Version_1_6_0, (void **)&rdoc_api) || !rdoc_api) {
        log_line("rdoc_autocapture_api=getapi-failed");
        return;
    }
    const char *capfile = getenv("RDOC_AUTOCAPTURE_FILE");
    if (capfile && *capfile) rdoc_api->SetCaptureFilePathTemplate(capfile);
    rdoc_api->SetCaptureOptionU32(eRENDERDOC_Option_APIValidation, 0);
    rdoc_api->SetCaptureOptionU32(eRENDERDOC_Option_CaptureAllCmdLists, 1);
    log_line("rdoc_autocapture_api=ready");
}

static void maybe_start_capture(const char *source) {
    if (capture_started || capture_finished) return;
    load_renderdoc_api();
    if (!rdoc_api) return;
    capture_started = 1;
    capture_start_source = source;
    if (env_enabled("RDOC_AUTOCAPTURE_TRIGGER_ONLY")) {
        rdoc_api->TriggerCapture();
    } else {
        rdoc_api->StartFrameCapture(NULL, NULL);
    }
    char buf[160];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_start=%s submit=%llu present=%llu egl_swap=%llu",
        source, (unsigned long long)submit_count, (unsigned long long)present_count,
        (unsigned long long)egl_swap_count);
    log_line(buf);
}

static void maybe_end_capture(const char *source) {
    if (!capture_started || capture_finished || !rdoc_api) return;
    if (env_enabled("RDOC_AUTOCAPTURE_TRIGGER_ONLY")) {
        log_line("rdoc_autocapture_end=trigger-only-skip");
        return;
    }
    capture_finished = 1;
    capture_end_source = source;
    uint32_t ok = rdoc_api->EndFrameCapture(NULL, NULL);
    char buf[160];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_end=%s ok=%u submit=%llu present=%llu egl_swap=%llu",
        source, ok, (unsigned long long)submit_count, (unsigned long long)present_count,
        (unsigned long long)egl_swap_count);
    log_line(buf);
}

static void log_capture_summary(void) {
    const char *status = "not-started";
    if (capture_started && capture_finished) {
        status = "ended";
    } else if (capture_started && env_enabled("RDOC_AUTOCAPTURE_TRIGGER_ONLY")) {
        status = "trigger-only";
    } else if (capture_started) {
        status = "started-not-ended";
    }
    char buf[2304];
    snprintf(buf, sizeof(buf),
        "rdoc_autocapture_summary=status:%s api:%u started:%u finished:%u start_source:%s end_source:%s submit:%llu present:%llu egl_swap:%llu egl_prepare_swap:%llu egl_wait_scheduled:%llu egl_vk_lock:%llu egl_vk_unlock:%llu egl_make_current:%llu egl_create_window_surface:%llu egl_create_platform_window_surface:%llu egl_get_display:%llu egl_get_platform_display:%llu egl_initialize:%llu egl_initialize_return:%llu egl_initialize_success:%llu egl_initialize_fail:%llu egl_initialize_last_result:%d egl_initialize_last_error:%d egl_choose_config:%llu vk_create_instance:%llu vk_create_device:%llu vk_enum_physical_device:%llu vk_enum_physical_device_return:%llu vk_enum_physical_device_last_result:%d vk_enum_physical_device_last_count:%u vk_get_physical_device_properties:%llu vk_get_physical_device_properties2:%llu vk_get_physical_device_features2:%llu vk_get_physical_device_queue_family:%llu vk_get_physical_device_queue_family2:%llu vk_get_physical_device_queue_family_last_count:%u vk_get_physical_device_queue_family2_last_count:%u vk_enum_device_extension:%llu vk_enum_device_extension_return:%llu vk_enum_device_extension_last_result:%d vk_enum_device_extension_last_count:%u vk_enum_instance_layer:%llu vk_enum_instance_extension:%llu proc_trace:%llu",
        status,
        rdoc_api ? 1u : 0u,
        capture_started ? 1u : 0u,
        capture_finished ? 1u : 0u,
        capture_start_source ? capture_start_source : "none",
        capture_end_source ? capture_end_source : "none",
        (unsigned long long)submit_count,
        (unsigned long long)present_count,
        (unsigned long long)egl_swap_count,
        (unsigned long long)egl_prepare_swap_count,
        (unsigned long long)egl_wait_scheduled_count,
        (unsigned long long)egl_vulkan_queue_lock_count,
        (unsigned long long)egl_vulkan_queue_unlock_count,
        (unsigned long long)egl_make_current_count,
        (unsigned long long)egl_create_window_surface_count,
        (unsigned long long)egl_create_platform_window_surface_count,
        (unsigned long long)egl_get_display_count,
        (unsigned long long)egl_get_platform_display_count,
        (unsigned long long)egl_initialize_count,
        (unsigned long long)egl_initialize_return_count,
        (unsigned long long)egl_initialize_success_count,
        (unsigned long long)egl_initialize_fail_count,
        egl_initialize_last_result,
        egl_initialize_last_error,
        (unsigned long long)egl_choose_config_count,
        (unsigned long long)vk_create_instance_count,
        (unsigned long long)vk_create_device_count,
        (unsigned long long)vk_enum_physical_device_count,
        (unsigned long long)vk_enum_physical_device_return_count,
        vk_enum_physical_device_last_result,
        vk_enum_physical_device_last_count,
        (unsigned long long)vk_get_physical_device_properties_count,
        (unsigned long long)vk_get_physical_device_properties2_count,
        (unsigned long long)vk_get_physical_device_features2_count,
        (unsigned long long)vk_get_physical_device_queue_family_count,
        (unsigned long long)vk_get_physical_device_queue_family2_count,
        vk_get_physical_device_queue_family_last_count,
        vk_get_physical_device_queue_family2_last_count,
        (unsigned long long)vk_enum_device_extension_count,
        (unsigned long long)vk_enum_device_extension_return_count,
        vk_enum_device_extension_last_result,
        vk_enum_device_extension_last_count,
        (unsigned long long)vk_enum_instance_layer_count,
        (unsigned long long)vk_enum_instance_extension_count,
        (unsigned long long)proc_trace_count);
    log_line(buf);
}

static void handle_autocapture_signal(int signum) {
    char buf[80];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_signal=%d", signum);
    log_line(buf);
    maybe_end_capture("signal");
    log_capture_summary();
    signal(signum, SIG_DFL);
    raise(signum);
}

static uint64_t env_u64(const char *name, uint64_t fallback) {
    const char *value = getenv(name);
    if (!value || !*value) return fallback;
    char *end = NULL;
    unsigned long long parsed = strtoull(value, &end, 10);
    if (end == value) return fallback;
    return (uint64_t)parsed;
}

static int env_enabled(const char *name) {
    const char *value = getenv(name);
    if (!value || !*value) return 0;
    return strcmp(value, "1") == 0 || strcmp(value, "true") == 0 || strcmp(value, "yes") == 0;
}

static int is_egl_intercept_symbol(const char *name) {
    if (!name) return 0;
    return strncmp(name, "egl", 3) == 0 ||
        strncmp(name, "EGL_", 4) == 0 ||
        strcmp(name, "eglLockVulkanQueueANGLE") == 0 ||
        strcmp(name, "eglUnlockVulkanQueueANGLE") == 0 ||
        strcmp(name, "eglPrepareSwapBuffersANGLE") == 0 ||
        strcmp(name, "eglWaitUntilWorkScheduledANGLE") == 0;
}

static int find_loaded_library_callback(struct dl_phdr_info *info, size_t size, void *data) {
    (void)size;
    struct library_lookup *lookup = (struct library_lookup *)data;
    if (!info->dlpi_name || !strstr(info->dlpi_name, lookup->needle)) return 0;
    lookup->base = (uintptr_t)info->dlpi_addr;
    snprintf(lookup->path, sizeof(lookup->path), "%s", info->dlpi_name);
    return 1;
}

static uintptr_t find_loaded_symbol_no_loader_lock(const char *library_hint, const char *symbol) {
    struct library_lookup lookup;
    memset(&lookup, 0, sizeof(lookup));
    lookup.needle = "librenderdoc.so";
    dl_iterate_phdr(find_loaded_library_callback, &lookup);
    if (!lookup.base) {
        log_line("rdoc_autocapture_elf=library-not-loaded");
        return 0;
    }

    const char *path = lookup.path[0] ? lookup.path : library_hint;
    if (!path || !*path) {
        log_line("rdoc_autocapture_elf=missing-path");
        return 0;
    }

    FILE *f = fopen(path, "rb");
    if (!f) {
        log_line("rdoc_autocapture_elf=open-failed");
        return 0;
    }
    if (fseek(f, 0, SEEK_END) != 0) {
        fclose(f);
        log_line("rdoc_autocapture_elf=seek-end-failed");
        return 0;
    }
    long len = ftell(f);
    if (len <= 0) {
        fclose(f);
        log_line("rdoc_autocapture_elf=size-failed");
        return 0;
    }
    rewind(f);
    unsigned char *bytes = (unsigned char *)malloc((size_t)len);
    if (!bytes) {
        fclose(f);
        log_line("rdoc_autocapture_elf=alloc-failed");
        return 0;
    }
    if (fread(bytes, 1, (size_t)len, f) != (size_t)len) {
        free(bytes);
        fclose(f);
        log_line("rdoc_autocapture_elf=read-failed");
        return 0;
    }
    fclose(f);

    uintptr_t result = 0;
    if ((size_t)len < sizeof(Elf64_Ehdr)) {
        log_line("rdoc_autocapture_elf=too-small");
        free(bytes);
        return 0;
    }
    Elf64_Ehdr *eh = (Elf64_Ehdr *)bytes;
    if (memcmp(eh->e_ident, ELFMAG, SELFMAG) != 0 || eh->e_ident[EI_CLASS] != ELFCLASS64) {
        log_line("rdoc_autocapture_elf=not-elf64");
        free(bytes);
        return 0;
    }
    if (eh->e_shoff == 0 || eh->e_shentsize != sizeof(Elf64_Shdr) ||
        (size_t)eh->e_shoff + ((size_t)eh->e_shnum * sizeof(Elf64_Shdr)) > (size_t)len) {
        log_line("rdoc_autocapture_elf=bad-sections");
        free(bytes);
        return 0;
    }
    Elf64_Shdr *sections = (Elf64_Shdr *)(bytes + eh->e_shoff);
    for (uint16_t i = 0; i < eh->e_shnum; i++) {
        if (sections[i].sh_type != SHT_DYNSYM) continue;
        if (sections[i].sh_link >= eh->e_shnum) continue;
        Elf64_Shdr *symsec = &sections[i];
        Elf64_Shdr *strsec = &sections[symsec->sh_link];
        if (symsec->sh_offset + symsec->sh_size > (uint64_t)len ||
            strsec->sh_offset + strsec->sh_size > (uint64_t)len ||
            symsec->sh_entsize != sizeof(Elf64_Sym)) {
            continue;
        }
        Elf64_Sym *syms = (Elf64_Sym *)(bytes + symsec->sh_offset);
        const char *strings = (const char *)(bytes + strsec->sh_offset);
        size_t count = (size_t)(symsec->sh_size / symsec->sh_entsize);
        for (size_t n = 0; n < count; n++) {
            if (syms[n].st_name >= strsec->sh_size) continue;
            if (strcmp(strings + syms[n].st_name, symbol) == 0) {
                result = lookup.base + (uintptr_t)syms[n].st_value;
                break;
            }
        }
        if (result) break;
    }
    free(bytes);
    log_line(result ? "rdoc_autocapture_elf=symbol-found" : "rdoc_autocapture_elf=symbol-missing");
    return result;
}

static void *delayed_capture_thread(void *unused) {
    (void)unused;
    uint64_t start_ms = env_u64("RDOC_AUTOCAPTURE_DELAY_START_MS", 0);
    uint64_t duration_ms = env_u64("RDOC_AUTOCAPTURE_DELAY_DURATION_MS", 500);
    char buf[160];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_delay_wait=start_ms:%llu duration_ms:%llu",
        (unsigned long long)start_ms, (unsigned long long)duration_ms);
    log_line(buf);
    if (start_ms > 0) usleep((useconds_t)(start_ms * 1000));
    log_line("rdoc_autocapture_delay_wake=start");
    maybe_start_capture("delay");
    if (duration_ms > 0) usleep((useconds_t)(duration_ms * 1000));
    log_line("rdoc_autocapture_delay_wake=end");
    maybe_end_capture("delay");
    return NULL;
}

static void *summary_thread(void *unused) {
    (void)unused;
    uint64_t interval_ms = env_u64("RDOC_AUTOCAPTURE_SUMMARY_INTERVAL_MS", 0);
    if (interval_ms == 0) return NULL;
    for (;;) {
        usleep((useconds_t)(interval_ms * 1000));
        log_capture_summary();
        if (capture_finished) return NULL;
    }
}

static void maybe_start_summary_thread(void) {
    if (summary_thread_started) return;
    if (env_u64("RDOC_AUTOCAPTURE_SUMMARY_INTERVAL_MS", 0) == 0) return;
    summary_thread_started = 1;
    pthread_t thread;
    if (pthread_create(&thread, NULL, summary_thread, NULL) == 0) {
        pthread_detach(thread);
        log_line("rdoc_autocapture_summary_thread=started");
    } else {
        log_line("rdoc_autocapture_summary_thread=failed");
    }
}

static void maybe_start_delay_thread(void) {
    if (delay_thread_started) return;
    if (env_u64("RDOC_AUTOCAPTURE_DELAY_START_MS", 0) == 0) return;
    delay_thread_started = 1;
    pthread_t thread;
    if (pthread_create(&thread, NULL, delayed_capture_thread, NULL) == 0) {
        pthread_detach(thread);
        log_line("rdoc_autocapture_delay_thread=started");
    } else {
        log_line("rdoc_autocapture_delay_thread=failed");
    }
}

VKAPI_ATTR VkResult VKAPI_CALL vkQueueSubmit(
    VkQueue queue,
    uint32_t submitCount,
    const VkSubmitInfo *pSubmits,
    VkFence fence) {
    if (!real_vkQueueSubmit) {
        real_vkQueueSubmit = (PFN_vkQueueSubmit)real_next_symbol("vkQueueSubmit");
    }
    submit_count++;
    uint64_t start_after = env_u64("RDOC_AUTOCAPTURE_START_SUBMIT", 1);
    if (submit_count >= start_after) maybe_start_capture("submit");
    VkResult result = real_vkQueueSubmit(queue, submitCount, pSubmits, fence);
    uint64_t end_after = env_u64("RDOC_AUTOCAPTURE_END_SUBMIT", start_after + 1);
    if (submit_count >= end_after) maybe_end_capture("submit");
    return result;
}

VKAPI_ATTR VkResult VKAPI_CALL vkQueueSubmit2(
    VkQueue queue,
    uint32_t submitCount,
    const VkSubmitInfo2 *pSubmits,
    VkFence fence) {
    if (!real_vkQueueSubmit2) {
        real_vkQueueSubmit2 = (PFN_vkQueueSubmit2)real_next_symbol("vkQueueSubmit2");
    }
    if (!real_vkQueueSubmit2) {
        log_line("rdoc_autocapture_error=missing-vkQueueSubmit2");
        return VK_ERROR_INITIALIZATION_FAILED;
    }
    submit_count++;
    uint64_t start_after = env_u64("RDOC_AUTOCAPTURE_START_SUBMIT", 1);
    if (submit_count >= start_after) maybe_start_capture("submit2");
    VkResult result = real_vkQueueSubmit2(queue, submitCount, pSubmits, fence);
    uint64_t end_after = env_u64("RDOC_AUTOCAPTURE_END_SUBMIT", start_after + 1);
    if (submit_count >= end_after) maybe_end_capture("submit2");
    return result;
}

VKAPI_ATTR VkResult VKAPI_CALL vkQueueSubmit2KHR(
    VkQueue queue,
    uint32_t submitCount,
    const VkSubmitInfo2 *pSubmits,
    VkFence fence) {
    if (!real_vkQueueSubmit2KHR) {
        real_vkQueueSubmit2KHR = (PFN_vkQueueSubmit2KHR)real_next_symbol("vkQueueSubmit2KHR");
    }
    if (!real_vkQueueSubmit2KHR) {
        log_line("rdoc_autocapture_error=missing-vkQueueSubmit2KHR");
        return VK_ERROR_INITIALIZATION_FAILED;
    }
    submit_count++;
    uint64_t start_after = env_u64("RDOC_AUTOCAPTURE_START_SUBMIT", 1);
    if (submit_count >= start_after) maybe_start_capture("submit2khr");
    VkResult result = real_vkQueueSubmit2KHR(queue, submitCount, pSubmits, fence);
    uint64_t end_after = env_u64("RDOC_AUTOCAPTURE_END_SUBMIT", start_after + 1);
    if (submit_count >= end_after) maybe_end_capture("submit2khr");
    return result;
}

VKAPI_ATTR VkResult VKAPI_CALL vkQueuePresentKHR(
    VkQueue queue,
    const VkPresentInfoKHR *pPresentInfo) {
    if (!real_vkQueuePresentKHR) {
        real_vkQueuePresentKHR = (PFN_vkQueuePresentKHR)real_next_symbol("vkQueuePresentKHR");
    }
    present_count++;
    maybe_start_capture("present");
    VkResult result = real_vkQueuePresentKHR(queue, pPresentInfo);
    maybe_end_capture("present");
    return result;
}

int eglSwapBuffers(void *display, void *surface) {
    if (!real_eglSwapBuffers) {
        real_eglSwapBuffers = (egl_swap_buffers_fn_t)real_next_symbol("eglSwapBuffers");
    }
    egl_swap_count++;
    uint64_t start_after = env_u64("RDOC_AUTOCAPTURE_START_EGL_SWAP", 1);
    if (egl_swap_count >= start_after) maybe_start_capture("eglSwapBuffers");
    int result = real_eglSwapBuffers ? real_eglSwapBuffers(display, surface) : 0;
    uint64_t end_after = env_u64("RDOC_AUTOCAPTURE_END_EGL_SWAP", start_after + 1);
    if (egl_swap_count >= end_after) maybe_end_capture("eglSwapBuffers");
    return result;
}

void *eglGetProcAddress(const char *procname) {
    if (!real_eglGetProcAddress) {
        real_eglGetProcAddress = (egl_get_proc_address_fn_t)real_next_symbol("eglGetProcAddress");
    }
    trace_proc_name("eglgetproc", procname);
    if (env_enabled("RDOC_AUTOCAPTURE_DISABLE_EGL_WRAP") &&
        (!procname || strcmp(procname, "vkGetInstanceProcAddr") != 0)) {
        return real_eglGetProcAddress ? real_eglGetProcAddress(procname) : NULL;
    }
    if (procname && (strcmp(procname, "eglSwapBuffers") == 0 || strcmp(procname, "EGL_SwapBuffers") == 0)) {
        if (!real_eglSwapBuffers && real_eglGetProcAddress) {
            real_eglSwapBuffers = (egl_swap_buffers_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglSwapBuffers");
        return (void *)eglSwapBuffers;
    }
    if (procname && strcmp(procname, "vkGetInstanceProcAddr") == 0) {
        log_line("rdoc_autocapture_eglgetproc=vkGetInstanceProcAddr");
        return (void *)vkGetInstanceProcAddr;
    }
    if (procname && (strcmp(procname, "eglGetDisplay") == 0 || strcmp(procname, "EGL_GetDisplay") == 0)) {
        if (!real_eglGetDisplay && real_eglGetProcAddress) {
            real_eglGetDisplay = (egl_get_display_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglGetDisplay");
        return (void *)eglGetDisplay;
    }
    if (procname && (strcmp(procname, "eglGetPlatformDisplay") == 0 ||
        strcmp(procname, "EGL_GetPlatformDisplay") == 0)) {
        if (!real_eglGetPlatformDisplay && real_eglGetProcAddress) {
            real_eglGetPlatformDisplay = (egl_get_platform_display_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglGetPlatformDisplay");
        return (void *)eglGetPlatformDisplay;
    }
    if (procname && (strcmp(procname, "eglInitialize") == 0 || strcmp(procname, "EGL_Initialize") == 0)) {
        if (!real_eglInitialize && real_eglGetProcAddress) {
            real_eglInitialize = (egl_initialize_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglInitialize");
        return (void *)eglInitialize;
    }
    if (procname && (strcmp(procname, "eglGetError") == 0 || strcmp(procname, "EGL_GetError") == 0)) {
        if (!real_eglGetError && real_eglGetProcAddress) {
            real_eglGetError = (egl_get_error_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglGetError");
        return (void *)eglGetError;
    }
    if (procname && (strcmp(procname, "eglChooseConfig") == 0 || strcmp(procname, "EGL_ChooseConfig") == 0)) {
        if (!real_eglChooseConfig && real_eglGetProcAddress) {
            real_eglChooseConfig = (egl_choose_config_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglChooseConfig");
        return (void *)eglChooseConfig;
    }
    if (procname && (strcmp(procname, "eglMakeCurrent") == 0 || strcmp(procname, "EGL_MakeCurrent") == 0)) {
        if (!real_eglMakeCurrent && real_eglGetProcAddress) {
            real_eglMakeCurrent = (egl_make_current_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglMakeCurrent");
        return (void *)eglMakeCurrent;
    }
    if (procname && (strcmp(procname, "eglCreateWindowSurface") == 0 ||
        strcmp(procname, "EGL_CreateWindowSurface") == 0)) {
        if (!real_eglCreateWindowSurface && real_eglGetProcAddress) {
            real_eglCreateWindowSurface = (egl_create_window_surface_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglCreateWindowSurface");
        return (void *)eglCreateWindowSurface;
    }
    if (procname && (strcmp(procname, "eglCreatePlatformWindowSurface") == 0 ||
        strcmp(procname, "EGL_CreatePlatformWindowSurface") == 0)) {
        if (!real_eglCreatePlatformWindowSurface && real_eglGetProcAddress) {
            real_eglCreatePlatformWindowSurface = (egl_create_window_surface_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglCreatePlatformWindowSurface");
        return (void *)eglCreatePlatformWindowSurface;
    }
    if (procname && strcmp(procname, "eglLockVulkanQueueANGLE") == 0) {
        if (!real_eglLockVulkanQueueANGLE && real_eglGetProcAddress) {
            real_eglLockVulkanQueueANGLE = (egl_vulkan_queue_lock_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglLockVulkanQueueANGLE");
        return (void *)eglLockVulkanQueueANGLE;
    }
    if (procname && strcmp(procname, "eglUnlockVulkanQueueANGLE") == 0) {
        if (!real_eglUnlockVulkanQueueANGLE && real_eglGetProcAddress) {
            real_eglUnlockVulkanQueueANGLE = (egl_vulkan_queue_lock_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglUnlockVulkanQueueANGLE");
        return (void *)eglUnlockVulkanQueueANGLE;
    }
    if (procname && (strcmp(procname, "eglPrepareSwapBuffersANGLE") == 0 ||
        strcmp(procname, "EGL_PrepareSwapBuffersANGLE") == 0)) {
        if (!real_eglPrepareSwapBuffersANGLE && real_eglGetProcAddress) {
            real_eglPrepareSwapBuffersANGLE = (egl_display_surface_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglPrepareSwapBuffersANGLE");
        return (void *)eglPrepareSwapBuffersANGLE;
    }
    if (procname && (strcmp(procname, "eglWaitUntilWorkScheduledANGLE") == 0 ||
        strcmp(procname, "EGL_WaitUntilWorkScheduledANGLE") == 0)) {
        if (!real_eglWaitUntilWorkScheduledANGLE && real_eglGetProcAddress) {
            real_eglWaitUntilWorkScheduledANGLE = (egl_display_fn_t)real_eglGetProcAddress(procname);
        }
        log_line("rdoc_autocapture_eglgetproc=eglWaitUntilWorkScheduledANGLE");
        return (void *)eglWaitUntilWorkScheduledANGLE;
    }
    return real_eglGetProcAddress ? real_eglGetProcAddress(procname) : NULL;
}

void eglLockVulkanQueueANGLE(void *display) {
    if (!real_eglLockVulkanQueueANGLE) {
        real_eglLockVulkanQueueANGLE = (egl_vulkan_queue_lock_fn_t)real_next_symbol("eglLockVulkanQueueANGLE");
    }
    egl_vulkan_queue_lock_count++;
    uint64_t start_after = env_u64("RDOC_AUTOCAPTURE_START_EGL_VK_LOCK", 1);
    if (egl_vulkan_queue_lock_count >= start_after) maybe_start_capture("eglLockVulkanQueueANGLE");
    if (real_eglLockVulkanQueueANGLE) real_eglLockVulkanQueueANGLE(display);
}

void eglUnlockVulkanQueueANGLE(void *display) {
    if (!real_eglUnlockVulkanQueueANGLE) {
        real_eglUnlockVulkanQueueANGLE = (egl_vulkan_queue_lock_fn_t)real_next_symbol("eglUnlockVulkanQueueANGLE");
    }
    egl_vulkan_queue_unlock_count++;
    if (real_eglUnlockVulkanQueueANGLE) real_eglUnlockVulkanQueueANGLE(display);
    uint64_t end_after = env_u64("RDOC_AUTOCAPTURE_END_EGL_VK_UNLOCK", 1);
    if (egl_vulkan_queue_unlock_count >= end_after) maybe_end_capture("eglUnlockVulkanQueueANGLE");
}

int eglPrepareSwapBuffersANGLE(void *display, void *surface) {
    if (!real_eglPrepareSwapBuffersANGLE) {
        real_eglPrepareSwapBuffersANGLE = (egl_display_surface_fn_t)real_next_symbol("eglPrepareSwapBuffersANGLE");
    }
    egl_prepare_swap_count++;
    uint64_t start_after = env_u64("RDOC_AUTOCAPTURE_START_EGL_PREPARE_SWAP", 1);
    if (egl_prepare_swap_count >= start_after) maybe_start_capture("eglPrepareSwapBuffersANGLE");
    return real_eglPrepareSwapBuffersANGLE ? real_eglPrepareSwapBuffersANGLE(display, surface) : 0;
}

int eglWaitUntilWorkScheduledANGLE(void *display) {
    if (!real_eglWaitUntilWorkScheduledANGLE) {
        real_eglWaitUntilWorkScheduledANGLE = (egl_display_fn_t)real_next_symbol("eglWaitUntilWorkScheduledANGLE");
    }
    egl_wait_scheduled_count++;
    int result = real_eglWaitUntilWorkScheduledANGLE ? real_eglWaitUntilWorkScheduledANGLE(display) : 0;
    uint64_t end_after = env_u64("RDOC_AUTOCAPTURE_END_EGL_WAIT_SCHEDULED", 1);
    if (egl_wait_scheduled_count >= end_after) maybe_end_capture("eglWaitUntilWorkScheduledANGLE");
    return result;
}

int eglMakeCurrent(void *display, void *draw, void *read, void *context) {
    if (!real_eglMakeCurrent) {
        real_eglMakeCurrent = (egl_make_current_fn_t)real_next_symbol("eglMakeCurrent");
    }
    egl_make_current_count++;
    int result = real_eglMakeCurrent ? real_eglMakeCurrent(display, draw, read, context) : 0;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_egl_make_current=result:%d", result);
    log_line(buf);
    return result;
}

void *eglCreateWindowSurface(void *display, void *config, void *native_window, const void *attrib_list) {
    if (!real_eglCreateWindowSurface) {
        real_eglCreateWindowSurface = (egl_create_window_surface_fn_t)real_next_symbol("eglCreateWindowSurface");
    }
    egl_create_window_surface_count++;
    void *result = real_eglCreateWindowSurface ? real_eglCreateWindowSurface(display, config, native_window, attrib_list) : NULL;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_egl_create_window_surface=result:%u", result ? 1U : 0U);
    log_line(buf);
    return result;
}

void *eglCreatePlatformWindowSurface(void *display, void *config, void *native_window, const void *attrib_list) {
    if (!real_eglCreatePlatformWindowSurface) {
        real_eglCreatePlatformWindowSurface = (egl_create_window_surface_fn_t)real_next_symbol("eglCreatePlatformWindowSurface");
    }
    egl_create_platform_window_surface_count++;
    void *result = real_eglCreatePlatformWindowSurface ? real_eglCreatePlatformWindowSurface(display, config, native_window, attrib_list) : NULL;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_egl_create_platform_window_surface=result:%u", result ? 1U : 0U);
    log_line(buf);
    return result;
}

void *eglGetDisplay(void *native_display) {
    if (!real_eglGetDisplay) {
        real_eglGetDisplay = (egl_get_display_fn_t)real_next_symbol("eglGetDisplay");
    }
    egl_get_display_count++;
    void *result = real_eglGetDisplay ? real_eglGetDisplay(native_display) : NULL;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_egl_get_display=result:%u", result ? 1U : 0U);
    log_line(buf);
    return result;
}

void *eglGetPlatformDisplay(unsigned int platform, void *native_display, const void *attrib_list) {
    if (!real_eglGetPlatformDisplay) {
        real_eglGetPlatformDisplay = (egl_get_platform_display_fn_t)real_next_symbol("eglGetPlatformDisplay");
    }
    egl_get_platform_display_count++;
    void *result = real_eglGetPlatformDisplay ? real_eglGetPlatformDisplay(platform, native_display, attrib_list) : NULL;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_egl_get_platform_display=platform:%u result:%u", platform, result ? 1U : 0U);
    log_line(buf);
    return result;
}

int eglInitialize(void *display, int *major, int *minor) {
    if (!real_eglInitialize) {
        real_eglInitialize = (egl_initialize_fn_t)real_next_symbol("eglInitialize");
    }
    egl_initialize_count++;
    int result = real_eglInitialize ? real_eglInitialize(display, major, minor) : 0;
    egl_initialize_return_count++;
    egl_initialize_last_result = result;
    if (result) {
        egl_initialize_success_count++;
    } else {
        egl_initialize_fail_count++;
    }
    if (!real_eglGetError) {
        real_eglGetError = (egl_get_error_fn_t)real_next_symbol("eglGetError");
    }
    if (real_eglGetError) {
        egl_initialize_last_error = real_eglGetError();
    }
    char buf[256];
    snprintf(buf, sizeof(buf),
        "rdoc_autocapture_egl_initialize=result:%d major:%d minor:%d error:%d",
        result,
        major ? *major : -1,
        minor ? *minor : -1,
        egl_initialize_last_error);
    log_line(buf);
    return result;
}

int eglChooseConfig(void *display, const int *attrib_list, void *configs, int config_size, int *num_config) {
    if (!real_eglChooseConfig) {
        real_eglChooseConfig = (egl_choose_config_fn_t)real_next_symbol("eglChooseConfig");
    }
    egl_choose_config_count++;
    int result = real_eglChooseConfig ? real_eglChooseConfig(display, attrib_list, configs, config_size, num_config) : 0;
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_egl_choose_config=result:%d count:%d", result, num_config ? *num_config : -1);
    log_line(buf);
    return result;
}

int eglGetError(void) {
    if (!real_eglGetError) {
        real_eglGetError = (egl_get_error_fn_t)real_next_symbol("eglGetError");
    }
    return real_eglGetError ? real_eglGetError() : 0x3000;
}

VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateInstanceLayerProperties(
    uint32_t *pPropertyCount,
    VkLayerProperties *pProperties) {
    if (!real_vkEnumerateInstanceLayerProperties) {
        real_vkEnumerateInstanceLayerProperties = (PFN_vkEnumerateInstanceLayerProperties)real_next_symbol("vkEnumerateInstanceLayerProperties");
    }
    vk_enum_instance_layer_count++;
    if (!real_vkEnumerateInstanceLayerProperties) return VK_ERROR_INITIALIZATION_FAILED;
    return real_vkEnumerateInstanceLayerProperties(pPropertyCount, pProperties);
}

VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateInstanceExtensionProperties(
    const char *pLayerName,
    uint32_t *pPropertyCount,
    VkExtensionProperties *pProperties) {
    if (!real_vkEnumerateInstanceExtensionProperties) {
        real_vkEnumerateInstanceExtensionProperties = (PFN_vkEnumerateInstanceExtensionProperties)real_next_symbol("vkEnumerateInstanceExtensionProperties");
    }
    vk_enum_instance_extension_count++;
    if (!real_vkEnumerateInstanceExtensionProperties) return VK_ERROR_INITIALIZATION_FAILED;
    VkResult result = real_vkEnumerateInstanceExtensionProperties(pLayerName, pPropertyCount, pProperties);
    log_extension_properties("instance", vk_enum_instance_extension_count, pLayerName, result, pPropertyCount, pProperties);
    return result;
}

VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateInstanceVersion(uint32_t *pApiVersion) {
    if (!real_vkEnumerateInstanceVersion) {
        real_vkEnumerateInstanceVersion = (PFN_vkEnumerateInstanceVersion)real_next_symbol("vkEnumerateInstanceVersion");
    }
    if (!real_vkEnumerateInstanceVersion) return VK_ERROR_INITIALIZATION_FAILED;
    VkResult result = real_vkEnumerateInstanceVersion(pApiVersion);
    char buf[256];
    snprintf(buf, sizeof(buf),
        "rdoc_autocapture_instance_version=result:%d version:%u",
        (int)result,
        pApiVersion ? (unsigned int)*pApiVersion : 0U);
    log_line(buf);
    return result;
}

VKAPI_ATTR VkResult VKAPI_CALL vkCreateInstance(
    const VkInstanceCreateInfo *pCreateInfo,
    const VkAllocationCallbacks *pAllocator,
    VkInstance *pInstance) {
    if (!real_vkCreateInstance) {
        real_vkCreateInstance = (PFN_vkCreateInstance)real_next_symbol("vkCreateInstance");
    }
    vk_create_instance_count++;
    if (pCreateInfo) {
        log_string_list("create_instance_extension", pCreateInfo->ppEnabledExtensionNames, pCreateInfo->enabledExtensionCount);
        log_string_list("create_instance_layer", pCreateInfo->ppEnabledLayerNames, pCreateInfo->enabledLayerCount);
    }
    if (!real_vkCreateInstance) return VK_ERROR_INITIALIZATION_FAILED;
    VkResult result = real_vkCreateInstance(pCreateInfo, pAllocator, pInstance);
    char buf[256];
    snprintf(buf, sizeof(buf), "rdoc_autocapture_create_instance_result=%d instance:%u", (int)result, pInstance && *pInstance ? 1U : 0U);
    log_line(buf);
    return result;
}

VKAPI_ATTR VkResult VKAPI_CALL vkCreateDevice(
    VkPhysicalDevice physicalDevice,
    const VkDeviceCreateInfo *pCreateInfo,
    const VkAllocationCallbacks *pAllocator,
    VkDevice *pDevice) {
    if (!real_vkCreateDevice) {
        real_vkCreateDevice = (PFN_vkCreateDevice)real_next_symbol("vkCreateDevice");
    }
    vk_create_device_count++;
    if (!real_vkCreateDevice) return VK_ERROR_INITIALIZATION_FAILED;
    return real_vkCreateDevice(physicalDevice, pCreateInfo, pAllocator, pDevice);
}

VKAPI_ATTR VkResult VKAPI_CALL vkEnumeratePhysicalDevices(
    VkInstance instance,
    uint32_t *pPhysicalDeviceCount,
    VkPhysicalDevice *pPhysicalDevices) {
    if (!real_vkEnumeratePhysicalDevices) {
        real_vkEnumeratePhysicalDevices = (PFN_vkEnumeratePhysicalDevices)real_next_symbol("vkEnumeratePhysicalDevices");
    }
    vk_enum_physical_device_count++;
    if (!real_vkEnumeratePhysicalDevices) return VK_ERROR_INITIALIZATION_FAILED;
    VkResult result = real_vkEnumeratePhysicalDevices(instance, pPhysicalDeviceCount, pPhysicalDevices);
    vk_enum_physical_device_return_count++;
    vk_enum_physical_device_last_result = (int)result;
    if (pPhysicalDeviceCount) vk_enum_physical_device_last_count = *pPhysicalDeviceCount;
    return result;
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceProperties(
    VkPhysicalDevice physicalDevice,
    VkPhysicalDeviceProperties *pProperties) {
    if (!real_vkGetPhysicalDeviceProperties) {
        real_vkGetPhysicalDeviceProperties = (PFN_vkGetPhysicalDeviceProperties)real_next_symbol("vkGetPhysicalDeviceProperties");
    }
    vk_get_physical_device_properties_count++;
    if (real_vkGetPhysicalDeviceProperties) {
        real_vkGetPhysicalDeviceProperties(physicalDevice, pProperties);
        if (pProperties) {
            char name[VK_MAX_PHYSICAL_DEVICE_NAME_SIZE];
            snprintf(name, sizeof(name), "%s", pProperties->deviceName);
            sanitize_log_value(name);
            char buf[512];
            snprintf(buf, sizeof(buf),
                "rdoc_autocapture_physical_device_properties=index:%llu type:%u vendor:%u device:%u api:%u driver:%u name:%s",
                (unsigned long long)vk_get_physical_device_properties_count,
                (unsigned int)pProperties->deviceType,
                (unsigned int)pProperties->vendorID,
                (unsigned int)pProperties->deviceID,
                (unsigned int)pProperties->apiVersion,
                (unsigned int)pProperties->driverVersion,
                name);
            log_line(buf);
        }
    }
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceProperties2(
    VkPhysicalDevice physicalDevice,
    VkPhysicalDeviceProperties2 *pProperties) {
    if (!real_vkGetPhysicalDeviceProperties2) {
        real_vkGetPhysicalDeviceProperties2 = (PFN_vkGetPhysicalDeviceProperties2)real_next_symbol("vkGetPhysicalDeviceProperties2");
    }
    vk_get_physical_device_properties2_count++;
    if (real_vkGetPhysicalDeviceProperties2) {
        real_vkGetPhysicalDeviceProperties2(physicalDevice, pProperties);
        log_physical_device_properties2(pProperties);
    }
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceProperties2KHR(
    VkPhysicalDevice physicalDevice,
    VkPhysicalDeviceProperties2 *pProperties) {
    if (!real_vkGetPhysicalDeviceProperties2KHR) {
        real_vkGetPhysicalDeviceProperties2KHR = (PFN_vkGetPhysicalDeviceProperties2KHR)real_next_symbol("vkGetPhysicalDeviceProperties2KHR");
    }
    vk_get_physical_device_properties2_count++;
    if (real_vkGetPhysicalDeviceProperties2KHR) {
        real_vkGetPhysicalDeviceProperties2KHR(physicalDevice, pProperties);
        log_physical_device_properties2(pProperties);
    }
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceFeatures2(
    VkPhysicalDevice physicalDevice,
    VkPhysicalDeviceFeatures2 *pFeatures) {
    if (!real_vkGetPhysicalDeviceFeatures2) {
        real_vkGetPhysicalDeviceFeatures2 = (PFN_vkGetPhysicalDeviceFeatures2)real_next_symbol("vkGetPhysicalDeviceFeatures2");
    }
    vk_get_physical_device_features2_count++;
    if (real_vkGetPhysicalDeviceFeatures2) real_vkGetPhysicalDeviceFeatures2(physicalDevice, pFeatures);
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceFeatures2KHR(
    VkPhysicalDevice physicalDevice,
    VkPhysicalDeviceFeatures2 *pFeatures) {
    if (!real_vkGetPhysicalDeviceFeatures2KHR) {
        real_vkGetPhysicalDeviceFeatures2KHR = (PFN_vkGetPhysicalDeviceFeatures2KHR)real_next_symbol("vkGetPhysicalDeviceFeatures2KHR");
    }
    vk_get_physical_device_features2_count++;
    if (real_vkGetPhysicalDeviceFeatures2KHR) real_vkGetPhysicalDeviceFeatures2KHR(physicalDevice, pFeatures);
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceQueueFamilyProperties(
    VkPhysicalDevice physicalDevice,
    uint32_t *pQueueFamilyPropertyCount,
    VkQueueFamilyProperties *pQueueFamilyProperties) {
    if (!real_vkGetPhysicalDeviceQueueFamilyProperties) {
        real_vkGetPhysicalDeviceQueueFamilyProperties = (PFN_vkGetPhysicalDeviceQueueFamilyProperties)real_next_symbol("vkGetPhysicalDeviceQueueFamilyProperties");
    }
    vk_get_physical_device_queue_family_count++;
    if (real_vkGetPhysicalDeviceQueueFamilyProperties) {
        real_vkGetPhysicalDeviceQueueFamilyProperties(physicalDevice, pQueueFamilyPropertyCount, pQueueFamilyProperties);
        if (pQueueFamilyPropertyCount) vk_get_physical_device_queue_family_last_count = *pQueueFamilyPropertyCount;
    }
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceQueueFamilyProperties2(
    VkPhysicalDevice physicalDevice,
    uint32_t *pQueueFamilyPropertyCount,
    VkQueueFamilyProperties2 *pQueueFamilyProperties) {
    if (!real_vkGetPhysicalDeviceQueueFamilyProperties2) {
        real_vkGetPhysicalDeviceQueueFamilyProperties2 = (PFN_vkGetPhysicalDeviceQueueFamilyProperties2)real_next_symbol("vkGetPhysicalDeviceQueueFamilyProperties2");
    }
    vk_get_physical_device_queue_family2_count++;
    if (real_vkGetPhysicalDeviceQueueFamilyProperties2) {
        real_vkGetPhysicalDeviceQueueFamilyProperties2(physicalDevice, pQueueFamilyPropertyCount, pQueueFamilyProperties);
        if (pQueueFamilyPropertyCount) vk_get_physical_device_queue_family2_last_count = *pQueueFamilyPropertyCount;
    }
}

VKAPI_ATTR void VKAPI_CALL vkGetPhysicalDeviceQueueFamilyProperties2KHR(
    VkPhysicalDevice physicalDevice,
    uint32_t *pQueueFamilyPropertyCount,
    VkQueueFamilyProperties2 *pQueueFamilyProperties) {
    if (!real_vkGetPhysicalDeviceQueueFamilyProperties2KHR) {
        real_vkGetPhysicalDeviceQueueFamilyProperties2KHR = (PFN_vkGetPhysicalDeviceQueueFamilyProperties2KHR)real_next_symbol("vkGetPhysicalDeviceQueueFamilyProperties2KHR");
    }
    vk_get_physical_device_queue_family2_count++;
    if (real_vkGetPhysicalDeviceQueueFamilyProperties2KHR) {
        real_vkGetPhysicalDeviceQueueFamilyProperties2KHR(physicalDevice, pQueueFamilyPropertyCount, pQueueFamilyProperties);
        if (pQueueFamilyPropertyCount) vk_get_physical_device_queue_family2_last_count = *pQueueFamilyPropertyCount;
    }
}

VKAPI_ATTR VkResult VKAPI_CALL vkEnumerateDeviceExtensionProperties(
    VkPhysicalDevice physicalDevice,
    const char *pLayerName,
    uint32_t *pPropertyCount,
    VkExtensionProperties *pProperties) {
    if (!real_vkEnumerateDeviceExtensionProperties) {
        real_vkEnumerateDeviceExtensionProperties = (PFN_vkEnumerateDeviceExtensionProperties)real_next_symbol("vkEnumerateDeviceExtensionProperties");
    }
    vk_enum_device_extension_count++;
    if (!real_vkEnumerateDeviceExtensionProperties) return VK_ERROR_INITIALIZATION_FAILED;
    VkResult result = real_vkEnumerateDeviceExtensionProperties(physicalDevice, pLayerName, pPropertyCount, pProperties);
    vk_enum_device_extension_return_count++;
    vk_enum_device_extension_last_result = (int)result;
    if (pPropertyCount) vk_enum_device_extension_last_count = *pPropertyCount;
    log_extension_properties("device", vk_enum_device_extension_count, pLayerName, result, pPropertyCount, pProperties);
    return result;
}

VKAPI_ATTR PFN_vkVoidFunction VKAPI_CALL vkGetDeviceProcAddr(
    VkDevice device,
    const char *pName) {
    trace_proc_name("gdpa", pName);
    trace_vulkan_proc_name("gdpa", pName);
    if (!real_vkGetDeviceProcAddr) {
        real_vkGetDeviceProcAddr = (PFN_vkGetDeviceProcAddr)real_next_symbol("vkGetDeviceProcAddr");
    }
    if (pName && strcmp(pName, "vkQueueSubmit") == 0) {
        if (real_vkGetDeviceProcAddr && !real_vkQueueSubmit) {
            real_vkQueueSubmit = (PFN_vkQueueSubmit)real_vkGetDeviceProcAddr(device, pName);
        }
        log_line("rdoc_autocapture_wrap=vkQueueSubmit");
        return (PFN_vkVoidFunction)vkQueueSubmit;
    }
    if (pName && strcmp(pName, "vkQueueSubmit2") == 0) {
        if (real_vkGetDeviceProcAddr && !real_vkQueueSubmit2) {
            real_vkQueueSubmit2 = (PFN_vkQueueSubmit2)real_vkGetDeviceProcAddr(device, pName);
        }
        log_line("rdoc_autocapture_wrap=vkQueueSubmit2");
        return (PFN_vkVoidFunction)vkQueueSubmit2;
    }
    if (pName && strcmp(pName, "vkQueueSubmit2KHR") == 0) {
        if (real_vkGetDeviceProcAddr && !real_vkQueueSubmit2KHR) {
            real_vkQueueSubmit2KHR = (PFN_vkQueueSubmit2KHR)real_vkGetDeviceProcAddr(device, pName);
        }
        log_line("rdoc_autocapture_wrap=vkQueueSubmit2KHR");
        return (PFN_vkVoidFunction)vkQueueSubmit2KHR;
    }
    if (pName && strcmp(pName, "vkQueuePresentKHR") == 0) {
        if (real_vkGetDeviceProcAddr && !real_vkQueuePresentKHR) {
            real_vkQueuePresentKHR = (PFN_vkQueuePresentKHR)real_vkGetDeviceProcAddr(device, pName);
        }
        log_line("rdoc_autocapture_wrap=vkQueuePresentKHR");
        return (PFN_vkVoidFunction)vkQueuePresentKHR;
    }
    if (pName && strcmp(pName, "vkCreateDevice") == 0) {
        if (real_vkGetDeviceProcAddr && !real_vkCreateDevice) {
            real_vkCreateDevice = (PFN_vkCreateDevice)real_vkGetDeviceProcAddr(device, pName);
        }
        log_line("rdoc_autocapture_wrap=vkCreateDevice");
        return (PFN_vkVoidFunction)vkCreateDevice;
    }
    if (!real_vkGetDeviceProcAddr) return NULL;
    PFN_vkVoidFunction result = real_vkGetDeviceProcAddr(device, pName);
    trace_vulkan_proc_result("gdpa", pName, result);
    return result;
}

VKAPI_ATTR PFN_vkVoidFunction VKAPI_CALL vkGetInstanceProcAddr(
    VkInstance instance,
    const char *pName) {
    trace_proc_name("gipa", pName);
    trace_vulkan_proc_name("gipa", pName);
    if (!real_vkGetInstanceProcAddr) {
        real_vkGetInstanceProcAddr = (PFN_vkGetInstanceProcAddr)real_next_symbol("vkGetInstanceProcAddr");
    }
    if (pName && strcmp(pName, "vkGetDeviceProcAddr") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetDeviceProcAddr");
        return (PFN_vkVoidFunction)vkGetDeviceProcAddr;
    }
    if (pName && strcmp(pName, "vkEnumerateInstanceLayerProperties") == 0) {
        log_line("rdoc_autocapture_wrap=vkEnumerateInstanceLayerProperties");
        return (PFN_vkVoidFunction)vkEnumerateInstanceLayerProperties;
    }
    if (pName && strcmp(pName, "vkEnumerateInstanceExtensionProperties") == 0) {
        log_line("rdoc_autocapture_wrap=vkEnumerateInstanceExtensionProperties");
        return (PFN_vkVoidFunction)vkEnumerateInstanceExtensionProperties;
    }
    if (pName && strcmp(pName, "vkCreateInstance") == 0) {
        log_line("rdoc_autocapture_wrap=vkCreateInstance");
        return (PFN_vkVoidFunction)vkCreateInstance;
    }
    if (pName && strcmp(pName, "vkEnumerateInstanceVersion") == 0) {
        log_line("rdoc_autocapture_wrap=vkEnumerateInstanceVersion");
        return (PFN_vkVoidFunction)vkEnumerateInstanceVersion;
    }
    if (pName && strcmp(pName, "vkCreateDevice") == 0) {
        log_line("rdoc_autocapture_wrap=vkCreateDevice-instance");
        return (PFN_vkVoidFunction)vkCreateDevice;
    }
    if (pName && strcmp(pName, "vkEnumeratePhysicalDevices") == 0) {
        log_line("rdoc_autocapture_wrap=vkEnumeratePhysicalDevices");
        return (PFN_vkVoidFunction)vkEnumeratePhysicalDevices;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceProperties") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceProperties");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceProperties;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceProperties2") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceProperties2");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceProperties2;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceProperties2KHR") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceProperties2KHR");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceProperties2KHR;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceFeatures2") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceFeatures2");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceFeatures2;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceFeatures2KHR") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceFeatures2KHR");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceFeatures2KHR;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceQueueFamilyProperties") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceQueueFamilyProperties");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceQueueFamilyProperties;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceQueueFamilyProperties2") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceQueueFamilyProperties2");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceQueueFamilyProperties2;
    }
    if (pName && strcmp(pName, "vkGetPhysicalDeviceQueueFamilyProperties2KHR") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetPhysicalDeviceQueueFamilyProperties2KHR");
        return (PFN_vkVoidFunction)vkGetPhysicalDeviceQueueFamilyProperties2KHR;
    }
    if (pName && strcmp(pName, "vkEnumerateDeviceExtensionProperties") == 0) {
        log_line("rdoc_autocapture_wrap=vkEnumerateDeviceExtensionProperties");
        return (PFN_vkVoidFunction)vkEnumerateDeviceExtensionProperties;
    }
    if (pName && strcmp(pName, "vkQueueSubmit") == 0) {
        log_line("rdoc_autocapture_wrap=vkQueueSubmit-instance");
        return (PFN_vkVoidFunction)vkQueueSubmit;
    }
    if (pName && strcmp(pName, "vkQueueSubmit2") == 0) {
        log_line("rdoc_autocapture_wrap=vkQueueSubmit2-instance");
        return (PFN_vkVoidFunction)vkQueueSubmit2;
    }
    if (pName && strcmp(pName, "vkQueueSubmit2KHR") == 0) {
        log_line("rdoc_autocapture_wrap=vkQueueSubmit2KHR-instance");
        return (PFN_vkVoidFunction)vkQueueSubmit2KHR;
    }
    if (pName && strcmp(pName, "vkQueuePresentKHR") == 0) {
        log_line("rdoc_autocapture_wrap=vkQueuePresentKHR-instance");
        return (PFN_vkVoidFunction)vkQueuePresentKHR;
    }
    if (!real_vkGetInstanceProcAddr) return NULL;
    PFN_vkVoidFunction result = real_vkGetInstanceProcAddr(instance, pName);
    trace_vulkan_proc_result("gipa", pName, result);
    return result;
}

void *dlsym(void *handle, const char *symbol) {
    trace_proc_name("dlsym", symbol);
    if (env_enabled("RDOC_AUTOCAPTURE_DISABLE_DLSYM_WRAP")) {
        return real_dlsym_lookup(handle, symbol);
    }
    if (env_enabled("RDOC_AUTOCAPTURE_DISABLE_EGL_WRAP") &&
        is_egl_intercept_symbol(symbol) &&
        strcmp(symbol, "eglGetProcAddress") != 0) {
        return real_dlsym_lookup(handle, symbol);
    }
    if (symbol && strcmp(symbol, "vkGetInstanceProcAddr") == 0) {
        if (!real_vkGetInstanceProcAddr) {
            real_vkGetInstanceProcAddr = (PFN_vkGetInstanceProcAddr)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetInstanceProcAddr");
        if (env_enabled("RDOC_AUTOCAPTURE_START_ON_DLSYM")) {
            maybe_start_capture("dlsym-vkGetInstanceProcAddr");
        }
        return (void *)vkGetInstanceProcAddr;
    }
    if (symbol && (strcmp(symbol, "eglSwapBuffers") == 0 || strcmp(symbol, "EGL_SwapBuffers") == 0)) {
        if (!real_eglSwapBuffers) {
            real_eglSwapBuffers = (egl_swap_buffers_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglSwapBuffers");
        return (void *)eglSwapBuffers;
    }
    if (symbol && strcmp(symbol, "eglGetProcAddress") == 0) {
        if (!real_eglGetProcAddress) {
            real_eglGetProcAddress = (egl_get_proc_address_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglGetProcAddress");
        return (void *)eglGetProcAddress;
    }
    if (symbol && (strcmp(symbol, "eglGetDisplay") == 0 || strcmp(symbol, "EGL_GetDisplay") == 0)) {
        if (!real_eglGetDisplay) {
            real_eglGetDisplay = (egl_get_display_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglGetDisplay");
        return (void *)eglGetDisplay;
    }
    if (symbol && (strcmp(symbol, "eglGetPlatformDisplay") == 0 ||
        strcmp(symbol, "EGL_GetPlatformDisplay") == 0)) {
        if (!real_eglGetPlatformDisplay) {
            real_eglGetPlatformDisplay = (egl_get_platform_display_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglGetPlatformDisplay");
        return (void *)eglGetPlatformDisplay;
    }
    if (symbol && (strcmp(symbol, "eglInitialize") == 0 || strcmp(symbol, "EGL_Initialize") == 0)) {
        if (!real_eglInitialize) {
            real_eglInitialize = (egl_initialize_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglInitialize");
        return (void *)eglInitialize;
    }
    if (symbol && (strcmp(symbol, "eglGetError") == 0 || strcmp(symbol, "EGL_GetError") == 0)) {
        if (!real_eglGetError) {
            real_eglGetError = (egl_get_error_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglGetError");
        return (void *)eglGetError;
    }
    if (symbol && (strcmp(symbol, "eglChooseConfig") == 0 || strcmp(symbol, "EGL_ChooseConfig") == 0)) {
        if (!real_eglChooseConfig) {
            real_eglChooseConfig = (egl_choose_config_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglChooseConfig");
        return (void *)eglChooseConfig;
    }
    if (symbol && (strcmp(symbol, "eglMakeCurrent") == 0 || strcmp(symbol, "EGL_MakeCurrent") == 0)) {
        if (!real_eglMakeCurrent) {
            real_eglMakeCurrent = (egl_make_current_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglMakeCurrent");
        return (void *)eglMakeCurrent;
    }
    if (symbol && (strcmp(symbol, "eglCreateWindowSurface") == 0 ||
        strcmp(symbol, "EGL_CreateWindowSurface") == 0)) {
        if (!real_eglCreateWindowSurface) {
            real_eglCreateWindowSurface = (egl_create_window_surface_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglCreateWindowSurface");
        return (void *)eglCreateWindowSurface;
    }
    if (symbol && (strcmp(symbol, "eglCreatePlatformWindowSurface") == 0 ||
        strcmp(symbol, "EGL_CreatePlatformWindowSurface") == 0)) {
        if (!real_eglCreatePlatformWindowSurface) {
            real_eglCreatePlatformWindowSurface = (egl_create_window_surface_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglCreatePlatformWindowSurface");
        return (void *)eglCreatePlatformWindowSurface;
    }
    if (symbol && strcmp(symbol, "eglLockVulkanQueueANGLE") == 0) {
        if (!real_eglLockVulkanQueueANGLE) {
            real_eglLockVulkanQueueANGLE = (egl_vulkan_queue_lock_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglLockVulkanQueueANGLE");
        return (void *)eglLockVulkanQueueANGLE;
    }
    if (symbol && strcmp(symbol, "eglUnlockVulkanQueueANGLE") == 0) {
        if (!real_eglUnlockVulkanQueueANGLE) {
            real_eglUnlockVulkanQueueANGLE = (egl_vulkan_queue_lock_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglUnlockVulkanQueueANGLE");
        return (void *)eglUnlockVulkanQueueANGLE;
    }
    if (symbol && (strcmp(symbol, "eglPrepareSwapBuffersANGLE") == 0 ||
        strcmp(symbol, "EGL_PrepareSwapBuffersANGLE") == 0)) {
        if (!real_eglPrepareSwapBuffersANGLE) {
            real_eglPrepareSwapBuffersANGLE = (egl_display_surface_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglPrepareSwapBuffersANGLE");
        return (void *)eglPrepareSwapBuffersANGLE;
    }
    if (symbol && (strcmp(symbol, "eglWaitUntilWorkScheduledANGLE") == 0 ||
        strcmp(symbol, "EGL_WaitUntilWorkScheduledANGLE") == 0)) {
        if (!real_eglWaitUntilWorkScheduledANGLE) {
            real_eglWaitUntilWorkScheduledANGLE = (egl_display_fn_t)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=eglWaitUntilWorkScheduledANGLE");
        return (void *)eglWaitUntilWorkScheduledANGLE;
    }
    if (symbol && strcmp(symbol, "vkGetDeviceProcAddr") == 0) {
        if (!real_vkGetDeviceProcAddr) {
            real_vkGetDeviceProcAddr = (PFN_vkGetDeviceProcAddr)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetDeviceProcAddr");
        return (void *)vkGetDeviceProcAddr;
    }
    if (symbol && strcmp(symbol, "vkEnumerateInstanceLayerProperties") == 0) {
        if (!real_vkEnumerateInstanceLayerProperties) {
            real_vkEnumerateInstanceLayerProperties = (PFN_vkEnumerateInstanceLayerProperties)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkEnumerateInstanceLayerProperties");
        return (void *)vkEnumerateInstanceLayerProperties;
    }
    if (symbol && strcmp(symbol, "vkEnumerateInstanceExtensionProperties") == 0) {
        if (!real_vkEnumerateInstanceExtensionProperties) {
            real_vkEnumerateInstanceExtensionProperties = (PFN_vkEnumerateInstanceExtensionProperties)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkEnumerateInstanceExtensionProperties");
        return (void *)vkEnumerateInstanceExtensionProperties;
    }
    if (symbol && strcmp(symbol, "vkCreateInstance") == 0) {
        if (!real_vkCreateInstance) {
            real_vkCreateInstance = (PFN_vkCreateInstance)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkCreateInstance");
        return (void *)vkCreateInstance;
    }
    if (symbol && strcmp(symbol, "vkEnumerateInstanceVersion") == 0) {
        if (!real_vkEnumerateInstanceVersion) {
            real_vkEnumerateInstanceVersion = (PFN_vkEnumerateInstanceVersion)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkEnumerateInstanceVersion");
        return (void *)vkEnumerateInstanceVersion;
    }
    if (symbol && strcmp(symbol, "vkCreateDevice") == 0) {
        if (!real_vkCreateDevice) {
            real_vkCreateDevice = (PFN_vkCreateDevice)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkCreateDevice");
        return (void *)vkCreateDevice;
    }
    if (symbol && strcmp(symbol, "vkEnumeratePhysicalDevices") == 0) {
        if (!real_vkEnumeratePhysicalDevices) {
            real_vkEnumeratePhysicalDevices = (PFN_vkEnumeratePhysicalDevices)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkEnumeratePhysicalDevices");
        return (void *)vkEnumeratePhysicalDevices;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceProperties") == 0) {
        if (!real_vkGetPhysicalDeviceProperties) {
            real_vkGetPhysicalDeviceProperties = (PFN_vkGetPhysicalDeviceProperties)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceProperties");
        return (void *)vkGetPhysicalDeviceProperties;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceProperties2") == 0) {
        if (!real_vkGetPhysicalDeviceProperties2) {
            real_vkGetPhysicalDeviceProperties2 = (PFN_vkGetPhysicalDeviceProperties2)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceProperties2");
        return (void *)vkGetPhysicalDeviceProperties2;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceProperties2KHR") == 0) {
        if (!real_vkGetPhysicalDeviceProperties2KHR) {
            real_vkGetPhysicalDeviceProperties2KHR = (PFN_vkGetPhysicalDeviceProperties2KHR)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceProperties2KHR");
        return (void *)vkGetPhysicalDeviceProperties2KHR;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceFeatures2") == 0) {
        if (!real_vkGetPhysicalDeviceFeatures2) {
            real_vkGetPhysicalDeviceFeatures2 = (PFN_vkGetPhysicalDeviceFeatures2)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceFeatures2");
        return (void *)vkGetPhysicalDeviceFeatures2;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceFeatures2KHR") == 0) {
        if (!real_vkGetPhysicalDeviceFeatures2KHR) {
            real_vkGetPhysicalDeviceFeatures2KHR = (PFN_vkGetPhysicalDeviceFeatures2KHR)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceFeatures2KHR");
        return (void *)vkGetPhysicalDeviceFeatures2KHR;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceQueueFamilyProperties") == 0) {
        if (!real_vkGetPhysicalDeviceQueueFamilyProperties) {
            real_vkGetPhysicalDeviceQueueFamilyProperties = (PFN_vkGetPhysicalDeviceQueueFamilyProperties)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceQueueFamilyProperties");
        return (void *)vkGetPhysicalDeviceQueueFamilyProperties;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceQueueFamilyProperties2") == 0) {
        if (!real_vkGetPhysicalDeviceQueueFamilyProperties2) {
            real_vkGetPhysicalDeviceQueueFamilyProperties2 = (PFN_vkGetPhysicalDeviceQueueFamilyProperties2)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceQueueFamilyProperties2");
        return (void *)vkGetPhysicalDeviceQueueFamilyProperties2;
    }
    if (symbol && strcmp(symbol, "vkGetPhysicalDeviceQueueFamilyProperties2KHR") == 0) {
        if (!real_vkGetPhysicalDeviceQueueFamilyProperties2KHR) {
            real_vkGetPhysicalDeviceQueueFamilyProperties2KHR = (PFN_vkGetPhysicalDeviceQueueFamilyProperties2KHR)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkGetPhysicalDeviceQueueFamilyProperties2KHR");
        return (void *)vkGetPhysicalDeviceQueueFamilyProperties2KHR;
    }
    if (symbol && strcmp(symbol, "vkEnumerateDeviceExtensionProperties") == 0) {
        if (!real_vkEnumerateDeviceExtensionProperties) {
            real_vkEnumerateDeviceExtensionProperties = (PFN_vkEnumerateDeviceExtensionProperties)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkEnumerateDeviceExtensionProperties");
        return (void *)vkEnumerateDeviceExtensionProperties;
    }
    if (symbol && strcmp(symbol, "vkQueueSubmit") == 0) {
        if (!real_vkQueueSubmit) {
            real_vkQueueSubmit = (PFN_vkQueueSubmit)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkQueueSubmit");
        return (void *)vkQueueSubmit;
    }
    if (symbol && strcmp(symbol, "vkQueueSubmit2") == 0) {
        if (!real_vkQueueSubmit2) {
            real_vkQueueSubmit2 = (PFN_vkQueueSubmit2)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkQueueSubmit2");
        return (void *)vkQueueSubmit2;
    }
    if (symbol && strcmp(symbol, "vkQueueSubmit2KHR") == 0) {
        if (!real_vkQueueSubmit2KHR) {
            real_vkQueueSubmit2KHR = (PFN_vkQueueSubmit2KHR)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkQueueSubmit2KHR");
        return (void *)vkQueueSubmit2KHR;
    }
    if (symbol && strcmp(symbol, "vkQueuePresentKHR") == 0) {
        if (!real_vkQueuePresentKHR) {
            real_vkQueuePresentKHR = (PFN_vkQueuePresentKHR)real_dlsym_lookup(handle, symbol);
        }
        log_line("rdoc_autocapture_dlsym=vkQueuePresentKHR");
        return (void *)vkQueuePresentKHR;
    }
    return real_dlsym_lookup(handle, symbol);
}

__attribute__((constructor))
static void rdoc_autocapture_init(void) {
    log_line("rdoc_autocapture_loaded=1");
    signal(SIGTERM, handle_autocapture_signal);
    signal(SIGINT, handle_autocapture_signal);
    maybe_start_summary_thread();
    maybe_start_delay_thread();
}

__attribute__((destructor))
static void rdoc_autocapture_fini(void) {
    maybe_end_capture("destructor");
    log_capture_summary();
}
