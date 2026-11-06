#ifndef SIMPLE_RUNTIME_DIRECTORY_BOUNDED_V1_H
#define SIMPLE_RUNTIME_DIRECTORY_BOUNDED_V1_H
/* Included by mutually exclusive runtime.c/core_exports providers. Tagged-text
 * ABI: path is one RuntimeValue, never ptr+len. No borrowed scratch escapes.
 * Errors: -1 invalid, -2 entries, -3 name bytes (including NUL), -4 I/O,
 * -5 unsupported, -6 allocation, -7 directory nofollow/type, -8 name encoding,
 * -9 live owner budget. Only complete EOF+successful closedir publishes a token.
 * Complete means iteration reached EOF, NOT an atomic namespace snapshot.
 * Ancestors must be trusted; O_NOFOLLOW protects the final directory component.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <errno.h>

#if !defined(_WIN32) && (defined(__linux__) || defined(__APPLE__) || defined(__FreeBSD__))
#include <dirent.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#include <pthread.h>

#ifndef SIMPLE_DIRECTORY_ALLOC_V1
#define SIMPLE_DIRECTORY_ALLOC_V1 malloc
#define SIMPLE_DIRECTORY_FREE_V1 free
#endif
#ifndef SIMPLE_DIRECTORY_READDIR_V1
#define SIMPLE_DIRECTORY_READDIR_V1 readdir
#endif
#ifndef SIMPLE_DIRECTORY_CLOSEDIR_V1
#define SIMPLE_DIRECTORY_CLOSEDIR_V1 closedir
#endif

typedef struct {
    char *name;
    int64_t kind;
    int64_t size;
} spl_directory_entry_v1;
typedef struct {
    spl_directory_entry_v1 *entries;
    int64_t count;
} spl_directory_listing_v1;
typedef struct {
    spl_directory_listing_v1 *listing;
    uint64_t generation;
    int reserved;
} spl_directory_slot_v1;
#define SPL_DIRECTORY_SLOTS_V1 64
static spl_directory_slot_v1 spl_directory_slots_v1[SPL_DIRECTORY_SLOTS_V1];
static pthread_mutex_t spl_directory_gate_v1 = PTHREAD_MUTEX_INITIALIZER;

static int64_t spl_directory_reserve_v1(void) {
    pthread_mutex_lock(&spl_directory_gate_v1);
    for (int i = 0; i < SPL_DIRECTORY_SLOTS_V1; ++i) {
        spl_directory_slot_v1 *s = &spl_directory_slots_v1[i];
        if (!s->reserved && s->generation < ((uint64_t)INT64_MAX - 64) / 64) {
            s->reserved = 1;
            ++s->generation;
            int64_t token = (int64_t)(s->generation * 64 + (uint64_t)i + 1);
            pthread_mutex_unlock(&spl_directory_gate_v1);
            return token;
        }
    }
    pthread_mutex_unlock(&spl_directory_gate_v1);
    return -9;
}
static spl_directory_slot_v1 *spl_directory_slot_locked_v1(int64_t token) {
    if (token <= 64) return NULL;
    uint64_t raw = (uint64_t)token - 1;
    spl_directory_slot_v1 *s = &spl_directory_slots_v1[raw % 64];
    return s->reserved && s->generation == raw / 64 ? s : NULL;
}
static void spl_directory_destroy_v1(spl_directory_listing_v1 *listing) {
    if (!listing) return;
    for (int64_t i = 0; i < listing->count; ++i)
        SIMPLE_DIRECTORY_FREE_V1(listing->entries[i].name);
    SIMPLE_DIRECTORY_FREE_V1(listing->entries);
    SIMPLE_DIRECTORY_FREE_V1(listing);
}
static void spl_directory_abandon_v1(int64_t token, spl_directory_listing_v1 *listing) {
    spl_directory_destroy_v1(listing);
    pthread_mutex_lock(&spl_directory_gate_v1);
    spl_directory_slot_v1 *s = spl_directory_slot_locked_v1(token);
    if (s) { s->reserved = 0; s->listing = NULL; }
    pthread_mutex_unlock(&spl_directory_gate_v1);
}
static void spl_directory_publish_v1(int64_t token, spl_directory_listing_v1 *listing) {
    pthread_mutex_lock(&spl_directory_gate_v1);
    spl_directory_slot_v1 *s = spl_directory_slot_locked_v1(token);
    if (s) s->listing = listing;
    pthread_mutex_unlock(&spl_directory_gate_v1);
}
static spl_directory_listing_v1 *spl_directory_allocate_v1(int64_t entries) {
    spl_directory_listing_v1 *listing = SIMPLE_DIRECTORY_ALLOC_V1(sizeof(*listing));
    if (!listing) return NULL;
    listing->count = 0;
    listing->entries = NULL;
    if (entries > 0) {
        listing->entries = SIMPLE_DIRECTORY_ALLOC_V1((size_t)entries * sizeof(*listing->entries));
        if (!listing->entries) { SIMPLE_DIRECTORY_FREE_V1(listing); return NULL; }
    }
    return listing;
}
static int spl_directory_path_v1(int64_t value, char path[4096]) {
    int64_t n = rt_string_len(value);
    const uint8_t *p = rt_string_data(value);
    if (n <= 0 || n >= 4096 || !p || memchr(p, 0, (size_t)n)) return 0;
    memcpy(path, p, (size_t)n);
    /* A trailing separator must not turn a final symlink into an ancestor
     * that O_NOFOLLOW/lstat would otherwise follow. Keep the filesystem root. */
    while (n > 1 && path[n - 1] == '/') --n;
    path[n] = 0;
    return 1;
}
static int spl_directory_utf8_v1(const unsigned char *p, size_t n) {
    size_t i = 0;
    while (i < n) {
        uint32_t c = p[i++];
        if (c < 0x80) continue;
        uint32_t value, minimum;
        size_t rest;
        if (c >= 0xc2 && c <= 0xdf) { value = c & 31; rest = 1; minimum = 0x80; }
        else if (c >= 0xe0 && c <= 0xef) { value = c & 15; rest = 2; minimum = 0x800; }
        else if (c >= 0xf0 && c <= 0xf4) { value = c & 7; rest = 3; minimum = 0x10000; }
        else return 0;
        if (rest > n - i) return 0;
        while (rest--) {
            c = p[i++];
            if ((c & 0xc0) != 0x80) return 0;
            value = (value << 6) | (c & 63);
        }
        if (value < minimum || value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff)) return 0;
    }
    return 1;
}
static int64_t spl_directory_kind_v1(mode_t mode) {
    if (S_ISREG(mode)) return 1;
    if (S_ISDIR(mode)) return 2;
    if (S_ISLNK(mode)) return 3;
    return 4;
}

static int64_t spl_directory_list_bounded_v1(int64_t path_value, int64_t max_entries, int64_t max_name_bytes) {
    char path[4096];
    if (max_entries < 0 || max_entries > 65536 || max_name_bytes < 0 ||
        max_name_bytes > 16777216 || !spl_directory_path_v1(path_value, path)) return -1;
    int64_t token = spl_directory_reserve_v1();
    if (token < 0) return token;
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) {
        int64_t error = errno == ELOOP || errno == ENOTDIR ? -7 : -4;
        spl_directory_abandon_v1(token, NULL);
        return error;
    }
    DIR *directory = fdopendir(fd);
    if (!directory) { close(fd); spl_directory_abandon_v1(token, NULL); return -4; }
    spl_directory_listing_v1 *listing = spl_directory_allocate_v1(max_entries);
    if (!listing) {
        SIMPLE_DIRECTORY_CLOSEDIR_V1(directory);
        spl_directory_abandon_v1(token, NULL);
        return -6;
    }
    int64_t error = 0, name_bytes = 0;
    for (;;) {
        errno = 0;
        struct dirent *entry = SIMPLE_DIRECTORY_READDIR_V1(directory);
        if (!entry) { if (errno != 0) error = -4; break; }
        if (!strcmp(entry->d_name, ".") || !strcmp(entry->d_name, "..")) continue;
        if (listing->count >= max_entries) { error = -2; break; }
        size_t length = strlen(entry->d_name);
        if (length >= (size_t)(max_name_bytes - name_bytes)) { error = -3; break; }
        if (!spl_directory_utf8_v1((const unsigned char *)entry->d_name, length)) { error = -8; break; }
        struct stat st;
        if (fstatat(dirfd(directory), entry->d_name, &st, AT_SYMLINK_NOFOLLOW) != 0 || st.st_size < 0) {
            error = -4; break;
        }
        char *name = SIMPLE_DIRECTORY_ALLOC_V1(length + 1);
        if (!name) { error = -6; break; }
        memcpy(name, entry->d_name, length + 1);
        spl_directory_entry_v1 *out = &listing->entries[listing->count++];
        out->name = name; out->kind = spl_directory_kind_v1(st.st_mode); out->size = (int64_t)st.st_size;
        name_bytes += (int64_t)length + 1;
    }
    if (SIMPLE_DIRECTORY_CLOSEDIR_V1(directory) != 0) error = -4;
    if (error) { spl_directory_abandon_v1(token, listing); return error; }
    spl_directory_publish_v1(token, listing);
    return token;
}

static int64_t spl_directory_path_probe_v1(int64_t path_value) {
    char path[4096];
    if (!spl_directory_path_v1(path_value, path)) return -1;
    struct stat st;
    int missing = 0;
    if (lstat(path, &st) != 0) { if (errno == ENOENT) missing = 1; else return -4; }
    if (!missing && st.st_size < 0) return -4;
    int64_t token = spl_directory_reserve_v1();
    if (token < 0) return token;
    spl_directory_listing_v1 *listing = spl_directory_allocate_v1(1);
    if (!listing) { spl_directory_abandon_v1(token, NULL); return -6; }
    listing->entries[0].name = NULL;
    listing->entries[0].kind = missing ? 0 : spl_directory_kind_v1(st.st_mode);
    listing->entries[0].size = missing ? 0 : (int64_t)st.st_size;
    listing->count = 1;
    spl_directory_publish_v1(token, listing);
    return token;
}

static int64_t spl_directory_list_count_v1(int64_t token) {
    pthread_mutex_lock(&spl_directory_gate_v1);
    spl_directory_slot_v1 *s = spl_directory_slot_locked_v1(token);
    int64_t result = s && s->listing ? s->listing->count : -1;
    pthread_mutex_unlock(&spl_directory_gate_v1);
    return result;
}
static int64_t spl_directory_field_v1(int64_t token, int64_t index, int kind) {
    pthread_mutex_lock(&spl_directory_gate_v1);
    spl_directory_slot_v1 *s = spl_directory_slot_locked_v1(token);
    int64_t result = -1;
    if (s && s->listing && index >= 0 && index < s->listing->count)
        result = kind ? s->listing->entries[index].kind : s->listing->entries[index].size;
    pthread_mutex_unlock(&spl_directory_gate_v1);
    return result;
}
static int64_t spl_directory_entry_kind_v1(int64_t token, int64_t index) { return spl_directory_field_v1(token, index, 1); }
static int64_t spl_directory_entry_size_v1(int64_t token, int64_t index) { return spl_directory_field_v1(token, index, 0); }
static int64_t spl_directory_entry_name_v1(int64_t token, int64_t index) {
    pthread_mutex_lock(&spl_directory_gate_v1);
    spl_directory_slot_v1 *s = spl_directory_slot_locked_v1(token);
    const char *name = NULL;
    if (s && s->listing && index >= 0 && index < s->listing->count) name = s->listing->entries[index].name;
    int64_t result = rt_string_new((const uint8_t *)name, name ? (uint64_t)strlen(name) : 0);
    pthread_mutex_unlock(&spl_directory_gate_v1);
    return result;
}
static int64_t spl_directory_list_free_v1(int64_t token) {
    pthread_mutex_lock(&spl_directory_gate_v1);
    spl_directory_slot_v1 *s = spl_directory_slot_locked_v1(token);
    if (!s || !s->listing) { pthread_mutex_unlock(&spl_directory_gate_v1); return -1; }
    spl_directory_listing_v1 *listing = s->listing;
    s->listing = NULL; s->reserved = 0;
    pthread_mutex_unlock(&spl_directory_gate_v1);
    spl_directory_destroy_v1(listing);
    return 1;
}
#else
/* Unavailable hosts never claim an empty successful directory snapshot. */
static int64_t spl_directory_list_bounded_v1(int64_t p, int64_t e, int64_t b) { (void)p; (void)e; (void)b; return -5; }
static int64_t spl_directory_path_probe_v1(int64_t p) { (void)p; return -5; }
static int64_t spl_directory_list_count_v1(int64_t h) { (void)h; return -1; }
static int64_t spl_directory_entry_kind_v1(int64_t h, int64_t i) { (void)h; (void)i; return -1; }
static int64_t spl_directory_entry_size_v1(int64_t h, int64_t i) { (void)h; (void)i; return -1; }
static int64_t spl_directory_entry_name_v1(int64_t h, int64_t i) { (void)h; (void)i; return rt_string_new(NULL, 0); }
static int64_t spl_directory_list_free_v1(int64_t h) { (void)h; return -1; }
#endif
#endif
