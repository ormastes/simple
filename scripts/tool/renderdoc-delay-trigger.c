#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <string.h>
#include <link.h>
#include <elf.h>
#include <renderdoc_app.h>

typedef int (*renderdoc_get_api_fn_t)(int, void **);

struct library_lookup {
    const char *needle;
    uintptr_t base;
    char path[1024];
};

static int env_enabled(const char *name) {
    const char *value = getenv(name);
    return value && value[0] && value[0] != '0';
}

static uint64_t env_u64(const char *name, uint64_t fallback) {
    const char *value = getenv(name);
    if (!value || !value[0]) return fallback;
    char *end = NULL;
    unsigned long long parsed = strtoull(value, &end, 10);
    return end && *end == '\0' ? (uint64_t)parsed : fallback;
}

static void log_line(const char *msg) {
    const char *path = getenv("RDOC_DELAY_TRIGGER_LOG");
    if (!path || !*path) return;
    FILE *f = fopen(path, "a");
    if (!f) return;
    fprintf(f, "%s\n", msg);
    fclose(f);
}

static void log_u32(const char *key, uint32_t value) {
    char buf[128];
    snprintf(buf, sizeof(buf), "%s=%u", key, value);
    log_line(buf);
}

static void log_str_value(const char *key, const char *value) {
    char buf[512];
    snprintf(buf, sizeof(buf), "%s=%s", key, value && value[0] ? value : "");
    log_line(buf);
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
        log_line("rdoc_delay_trigger_elf=library-not-loaded");
        return 0;
    }

    const char *path = lookup.path[0] ? lookup.path : library_hint;
    if (!path || !*path) {
        log_line("rdoc_delay_trigger_elf=missing-path");
        return 0;
    }

    FILE *f = fopen(path, "rb");
    if (!f) {
        log_line("rdoc_delay_trigger_elf=open-failed");
        return 0;
    }
    if (fseek(f, 0, SEEK_END) != 0) {
        fclose(f);
        log_line("rdoc_delay_trigger_elf=seek-end-failed");
        return 0;
    }
    long len = ftell(f);
    if (len <= 0) {
        fclose(f);
        log_line("rdoc_delay_trigger_elf=size-failed");
        return 0;
    }
    rewind(f);
    unsigned char *bytes = (unsigned char *)malloc((size_t)len);
    if (!bytes) {
        fclose(f);
        log_line("rdoc_delay_trigger_elf=alloc-failed");
        return 0;
    }
    if (fread(bytes, 1, (size_t)len, f) != (size_t)len) {
        free(bytes);
        fclose(f);
        log_line("rdoc_delay_trigger_elf=read-failed");
        return 0;
    }
    fclose(f);

    uintptr_t result = 0;
    if ((size_t)len < sizeof(Elf64_Ehdr)) {
        log_line("rdoc_delay_trigger_elf=too-small");
        free(bytes);
        return 0;
    }
    Elf64_Ehdr *eh = (Elf64_Ehdr *)bytes;
    if (memcmp(eh->e_ident, ELFMAG, SELFMAG) != 0 || eh->e_ident[EI_CLASS] != ELFCLASS64) {
        log_line("rdoc_delay_trigger_elf=not-elf64");
        free(bytes);
        return 0;
    }
    if (eh->e_shoff == 0 || eh->e_shentsize != sizeof(Elf64_Shdr) ||
        (size_t)eh->e_shoff + ((size_t)eh->e_shnum * sizeof(Elf64_Shdr)) > (size_t)len) {
        log_line("rdoc_delay_trigger_elf=bad-sections");
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
    log_line(result ? "rdoc_delay_trigger_elf=symbol-found" : "rdoc_delay_trigger_elf=symbol-missing");
    return result;
}

static void *delay_trigger_thread(void *arg) {
    (void)arg;
    uint64_t start_ms = env_u64("RDOC_DELAY_TRIGGER_START_MS", 2000);
    uint64_t duration_ms = env_u64("RDOC_DELAY_TRIGGER_DURATION_MS", 2000);
    usleep((useconds_t)(start_ms * 1000));
    log_line("rdoc_delay_trigger=wake");

    const char *lib_path = getenv("RDOC_DELAY_TRIGGER_RENDERDOC_LIB");
    renderdoc_get_api_fn_t get_api = (renderdoc_get_api_fn_t)
        find_loaded_symbol_no_loader_lock(lib_path, "RENDERDOC_GetAPI");
    if (get_api) {
        log_line("rdoc_delay_trigger=getapi-elf-found");
    }

    void *handle = NULL;
    if (!get_api && lib_path && lib_path[0]) {
        log_line("rdoc_delay_trigger=dlopen-path-start");
        handle = dlopen(lib_path, RTLD_NOW | RTLD_LOCAL);
        log_line(handle ? "rdoc_delay_trigger=dlopen-path-found" : "rdoc_delay_trigger=dlopen-path-missing");
    }
    if (!get_api && !handle) {
        log_line("rdoc_delay_trigger=dlopen-name-start");
        handle = dlopen("librenderdoc.so", RTLD_NOW | RTLD_LOCAL);
        log_line(handle ? "rdoc_delay_trigger=dlopen-name-found" : "rdoc_delay_trigger=dlopen-name-missing");
    }
    if (!get_api && !handle) {
        log_line("rdoc_delay_trigger=missing-librenderdoc");
        return NULL;
    }

    if (!get_api) {
        get_api = (renderdoc_get_api_fn_t)dlsym(handle, "RENDERDOC_GetAPI");
    }
    if (!get_api) {
        log_line("rdoc_delay_trigger=missing-getapi");
        return NULL;
    }

    RENDERDOC_API_1_6_0 *api = NULL;
    if (!get_api(eRENDERDOC_API_Version_1_6_0, (void **)&api) || !api) {
        log_line("rdoc_delay_trigger=getapi-failed");
        return NULL;
    }

    log_line("rdoc_delay_trigger=api-ready");
    const char *capfile = getenv("RDOC_AUTOCAPTURE_FILE");
    if (capfile && capfile[0]) {
        api->SetCaptureFilePathTemplate(capfile);
        log_str_value("rdoc_delay_trigger_capfile_set", capfile);
    }
    log_str_value("rdoc_delay_trigger_capfile_template", api->GetCaptureFilePathTemplate());
    log_u32("rdoc_delay_trigger_num_captures_before", api->GetNumCaptures());
    log_u32("rdoc_delay_trigger_is_capturing_before", api->IsFrameCapturing());
    api->StartFrameCapture(NULL, NULL);
    log_line("rdoc_delay_trigger=start");
    log_u32("rdoc_delay_trigger_is_capturing_after_start", api->IsFrameCapturing());
    usleep((useconds_t)(duration_ms * 1000));
    log_u32("rdoc_delay_trigger_is_capturing_before_end", api->IsFrameCapturing());
    uint32_t ok = api->EndFrameCapture(NULL, NULL);
    log_u32("rdoc_delay_trigger_is_capturing_after_end", api->IsFrameCapturing());
    log_u32("rdoc_delay_trigger_num_captures_after", api->GetNumCaptures());
    char buf[96];
    snprintf(buf, sizeof(buf), "rdoc_delay_trigger=end ok=%u", ok);
    log_line(buf);
    return NULL;
}

__attribute__((constructor))
static void rdoc_delay_trigger_init(void) {
    log_line("rdoc_delay_trigger=loaded");
    if (!env_enabled("RDOC_DELAY_TRIGGER_ENABLE")) {
        log_line("rdoc_delay_trigger=disabled");
        return;
    }
    pthread_t thread;
    if (pthread_create(&thread, NULL, delay_trigger_thread, NULL) == 0) {
        pthread_detach(thread);
        log_line("rdoc_delay_trigger=thread-started");
    } else {
        log_line("rdoc_delay_trigger=thread-failed");
    }
}
