#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
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
static PFN_vkGetDeviceProcAddr real_vkGetDeviceProcAddr;
static PFN_vkGetInstanceProcAddr real_vkGetInstanceProcAddr;
typedef int (*egl_swap_buffers_fn_t)(void *, void *);
typedef void *(*egl_get_proc_address_fn_t)(const char *);
typedef void (*egl_vulkan_queue_lock_fn_t)(void *);
typedef int (*egl_display_surface_fn_t)(void *, void *);
typedef int (*egl_display_fn_t)(void *);
static egl_swap_buffers_fn_t real_eglSwapBuffers;
static egl_get_proc_address_fn_t real_eglGetProcAddress;
static egl_vulkan_queue_lock_fn_t real_eglLockVulkanQueueANGLE;
static egl_vulkan_queue_lock_fn_t real_eglUnlockVulkanQueueANGLE;
static egl_display_surface_fn_t real_eglPrepareSwapBuffersANGLE;
static egl_display_fn_t real_eglWaitUntilWorkScheduledANGLE;
typedef void *(*real_dlsym_fn_t)(void *, const char *);
static real_dlsym_fn_t real_dlsym_fn;
static int capture_started;
static int capture_finished;
static int delay_thread_started;
static const char *capture_start_source;
static const char *capture_end_source;
static uint64_t submit_count;
static uint64_t present_count;
static uint64_t egl_swap_count;
static uint64_t egl_vulkan_queue_lock_count;
static uint64_t egl_vulkan_queue_unlock_count;
static uint64_t egl_prepare_swap_count;
static uint64_t egl_wait_scheduled_count;
static uint64_t proc_trace_count;

static int env_enabled(const char *name);
static uint64_t env_u64(const char *name, uint64_t fallback);
static uintptr_t find_loaded_symbol_no_loader_lock(const char *library_hint, const char *symbol);
void eglLockVulkanQueueANGLE(void *display);
void eglUnlockVulkanQueueANGLE(void *display);
int eglPrepareSwapBuffersANGLE(void *display, void *surface);
int eglWaitUntilWorkScheduledANGLE(void *display);

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

static void *real_dlsym_lookup(void *handle, const char *symbol) {
    if (!real_dlsym_fn) {
        real_dlsym_fn = (real_dlsym_fn_t)dlvsym(RTLD_NEXT, "dlsym", "GLIBC_2.2.5");
    }
    if (!real_dlsym_fn) return NULL;
    return real_dlsym_fn(handle, symbol);
}

static void *real_next_symbol(const char *symbol) {
    return real_dlsym_lookup(RTLD_NEXT, symbol);
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
    char buf[384];
    snprintf(buf, sizeof(buf),
        "rdoc_autocapture_summary=status:%s api:%u started:%u finished:%u start_source:%s end_source:%s submit:%llu present:%llu egl_swap:%llu egl_prepare_swap:%llu egl_wait_scheduled:%llu egl_vk_lock:%llu egl_vk_unlock:%llu proc_trace:%llu",
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
        (unsigned long long)proc_trace_count);
    log_line(buf);
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

VKAPI_ATTR PFN_vkVoidFunction VKAPI_CALL vkGetDeviceProcAddr(
    VkDevice device,
    const char *pName) {
    trace_proc_name("gdpa", pName);
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
    if (!real_vkGetDeviceProcAddr) return NULL;
    return real_vkGetDeviceProcAddr(device, pName);
}

VKAPI_ATTR PFN_vkVoidFunction VKAPI_CALL vkGetInstanceProcAddr(
    VkInstance instance,
    const char *pName) {
    trace_proc_name("gipa", pName);
    if (!real_vkGetInstanceProcAddr) {
        real_vkGetInstanceProcAddr = (PFN_vkGetInstanceProcAddr)real_next_symbol("vkGetInstanceProcAddr");
    }
    if (pName && strcmp(pName, "vkGetDeviceProcAddr") == 0) {
        log_line("rdoc_autocapture_wrap=vkGetDeviceProcAddr");
        return (PFN_vkVoidFunction)vkGetDeviceProcAddr;
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
    return real_vkGetInstanceProcAddr(instance, pName);
}

void *dlsym(void *handle, const char *symbol) {
    trace_proc_name("dlsym", symbol);
    if (env_enabled("RDOC_AUTOCAPTURE_DISABLE_DLSYM_WRAP")) {
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
    maybe_start_delay_thread();
}

__attribute__((destructor))
static void rdoc_autocapture_fini(void) {
    maybe_end_capture("destructor");
    log_capture_summary();
}
