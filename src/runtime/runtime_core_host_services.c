/* Narrow hosted providers required by core-c-bootstrap tool closures.
 *
 * Keep these out of runtime_native.c: that translation unit is also used by
 * freestanding lanes.  The core-C capsule opts into this file explicitly.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif
/* macOS: _POSIX_C_SOURCE alone hides the BSD extensions in <unistd.h>, so
 * sysconf's _SC_NPROCESSORS_ONLN is undeclared and this file fails to compile
 * (`use of undeclared identifier '_SC_NPROCESSORS_ONLN'` at the sysconf call
 * below) -- which blocks the whole macOS Stage-2 bootstrap. _DARWIN_C_SOURCE
 * re-exposes them without widening anything on other platforms, where the
 * guard is inert. This has now regressed out of main TWICE via merges; if it
 * disappears again, look for a merge that reverted this hunk rather than an
 * intentional removal. */
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif
/* Linux: CPU_SET / pthread_setaffinity_np / sched_getcpu (thread pinning,
 * below) are GNU extensions. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif

#include "runtime.h"
#include "runtime_core_text_arg.h"

#include <errno.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#include <winioctl.h>
#include "platform/runtime_win_long_path.h"
#include "platform/spl_win_utf16_private.h"
#include "platform/windows_system_processor_count.h"
#include <sys/stat.h>
#ifndef SYMLINK_FLAG_RELATIVE
/* SymbolicLinkReparseBuffer.Flags bit 0 is the relative-target marker.
 * Some clang-cl Windows SDK views omit the symbolic name. */
#define SYMLINK_FLAG_RELATIVE 1u
#endif
#undef max
#else
#include <fcntl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <dirent.h>
#include <unistd.h>
#if defined(__FreeBSD__)
#include <sys/types.h>
#include <sys/sysctl.h>
#endif
#endif

static char* core_host_strdup(const char* value) {
    size_t length = strlen(value);
    char* result = (char*)malloc(length + 1);
    if (!result) return NULL;
    memcpy(result, value, length + 1);
    return result;
}

char* rt_hostname(void) {
#if defined(_WIN32)
    char buffer[256];
    DWORD length = (DWORD)sizeof(buffer);
    if (GetComputerNameA(buffer, &length)) {
        char* result = (char*)malloc((size_t)length + 1);
        if (!result) return NULL;
        memcpy(result, buffer, (size_t)length);
        result[length] = '\0';
        return result;
    }
#else
    char buffer[256];
    if (gethostname(buffer, sizeof(buffer)) == 0) {
        buffer[sizeof(buffer) - 1] = '\0';
        return core_host_strdup(buffer);
    }
#endif
    return core_host_strdup("localhost");
}

int64_t rt_unix_socket_connect(const char* path) {
#if defined(_WIN32)
    (void)path;
    return -1;
#else
    if (!path) return -1;
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    struct sockaddr_un address;
    memset(&address, 0, sizeof(address));
    address.sun_family = AF_UNIX;
    if (strlen(path) >= sizeof(address.sun_path)) {
        close(fd);
        return -1;
    }
    memcpy(address.sun_path, path, strlen(path) + 1);
    if (connect(fd, (struct sockaddr*)&address, sizeof(address)) != 0) {
        close(fd);
        return -1;
    }
    return (int64_t)fd;
#endif
}

int64_t rt_metal_is_available(void) {
    /* The portable core capsule has no Objective-C Metal provider. */
    return 0;
}

bool rt_is_debug_mode_enabled(void) {
    return false;
}

int64_t rt_file_stat(const uint8_t* path, uint64_t path_len) {
    if (!path || path_len == 0 || path_len >= 4096) return 0;
    char buffer[4096];
    memcpy(buffer, path, (size_t)path_len);
    buffer[path_len] = '\0';
    struct stat metadata;
    return stat(buffer, &metadata) == 0 ? (int64_t)metadata.st_mtime : 0;
}

bool rt_process_exists(int64_t pid) {
    if (pid <= 0) return false;
#if defined(_WIN32)
    HANDLE process = OpenProcess(SYNCHRONIZE | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, (DWORD)pid);
    if (!process) return GetLastError() == ERROR_ACCESS_DENIED;
    /* Not the exit code: exit 259 would read as STILL_ACTIVE forever. */
    DWORD status = WaitForSingleObject(process, 0);
    CloseHandle(process);
    return status == WAIT_TIMEOUT;
#else
    return kill((pid_t)pid, 0) == 0 || errno == EPERM;
#endif
}

/* ELF spellings emitted by the self-hosted method fallback. Keep these as
 * compatibility aliases while MIR lowering converges on the libm names. */
#if !defined(_WIN32)
double rt_f64_sqrt(double value) __asm__("f64.sqrt");
double rt_f64_floor(double value) __asm__("f64.floor");
double rt_f64_ceil(double value) __asm__("f64.ceil");
double rt_f64_sqrt(double value) { return sqrt(value); }
double rt_f64_floor(double value) { return floor(value); }
double rt_f64_ceil(double value) { return ceil(value); }
#endif

int64_t max(int64_t left, int64_t right) {
    return left > right ? left : right;
}

int32_t rt_package_chmod(const uint8_t* path, uint64_t path_len, int32_t mode) {
#if defined(_WIN32)
    (void)path;
    (void)path_len;
    (void)mode;
    return 0;
#else
    if (!path || path_len == 0 || path_len >= 4096) return -1;
    char buffer[4096];
    memcpy(buffer, path, (size_t)path_len);
    buffer[path_len] = '\0';
    return chmod(buffer, (mode_t)mode) == 0 ? 0 : -1;
#endif
}

/* Rest of the package_sffi.spl family (Rust twin: runtime value/sffi/package.rs).
 * Text args arrive as (ptr,len) pairs: every name below is in text_arg_indices
 * (src/compiler/50.mir/text_extern_abi.spl). Status returns follow the Rust
 * twin: 0 ok / -1 error; exists/is_dir answer 1/0, -1 for a null path. Each
 * body delegates to the long-path-aware file primitive in runtime_native.c. */
int64_t rt_package_sha256(const uint8_t* path, uint64_t path_len) {
    return rt_file_hash_sha256(path, path_len);
}

int64_t rt_package_file_size(const uint8_t* path, uint64_t path_len) {
    return rt_file_size(path, path_len);
}

int32_t rt_package_copy_file(const uint8_t* src, uint64_t src_len,
                             const uint8_t* dst, uint64_t dst_len) {
    return rt_file_copy(src, src_len, dst, dst_len) ? 0 : -1;
}

int32_t rt_package_mkdir_all(const uint8_t* path, uint64_t path_len) {
    return rt_dir_create_all(path, path_len) ? 0 : -1;
}

int32_t rt_package_remove_dir_all(const uint8_t* path, uint64_t path_len) {
    return rt_dir_remove_all(path, path_len) ? 0 : -1;
}

int32_t rt_package_exists(const uint8_t* path, uint64_t path_len) {
    if (!path) return -1;
    return rt_file_exists(path, path_len) ? 1 : 0;
}

int32_t rt_package_is_dir(const uint8_t* path, uint64_t path_len) {
    if (!path) return -1;
    return rt_dir_exists(path, path_len) ? 1 : 0;
}

int32_t rt_package_create_symlink(const uint8_t* target, uint64_t target_len,
                                  const uint8_t* link, uint64_t link_len) {
    if (!target || !link || target_len == 0 || link_len == 0 ||
        target_len >= 4096 || link_len >= 4096) return -1;
    char target_buf[4096];
    char link_buf[4096];
    memcpy(target_buf, target, (size_t)target_len);
    target_buf[target_len] = '\0';
    memcpy(link_buf, link, (size_t)link_len);
    link_buf[link_len] = '\0';
#if defined(_WIN32)
    /* Windows does not translate '/' when following a reparse point; store
     * native separators (same rule as the Rust twin's symlink_file). */
    for (char* p = target_buf; *p; p++) if (*p == '/') *p = (char)92;
    wchar_t target_w[4096];
    wchar_t link_w[4096];
    if (MultiByteToWideChar(CP_UTF8, 0, target_buf, -1, target_w, 4096) == 0) return -1;
    if (MultiByteToWideChar(CP_UTF8, 0, link_buf, -1, link_w, 4096) == 0) return -1;
    return CreateSymbolicLinkW(link_w, target_w, SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE) ? 0 : -1;
#else
    return symlink(target_buf, link_buf) == 0 ? 0 : -1;
#endif
}

/* .tar.gz create/extract (Rust twin: value/sffi/package.rs, flate2 + tar). The
 * C runtime carries no zlib, so the codec is local and dependency-free:
 *  - create writes a ustar archive inside a valid gzip stream made of stored
 *    (uncompressed) deflate blocks, so any gunzip/tar reads it back (larger
 *    than a compressed archive, never wrong);
 *  - extract has a full inflate (stored, fixed and dynamic Huffman blocks), so
 *    archives produced by the Rust twin or by tar/gzip are accepted.
 * Entries naming an absolute path, a drive, a backslash or a ".." component are
 * refused (-1), as the tar crate's unpack refuses to escape the destination. */
#define PKG_TAR_MAX_DEPTH 64
#define PKG_TAR_MAX_PATH 4096

static uint32_t pkg_crc32_update(uint32_t crc, const uint8_t* data, size_t len) {
    uint32_t table[256];
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t c = i;
        for (int k = 0; k < 8; k++) c = (c & 1u) ? (0xEDB88320u ^ (c >> 1)) : (c >> 1);
        table[i] = c;
    }
    crc = ~crc;
    for (size_t i = 0; i < len; i++) crc = table[(crc ^ data[i]) & 0xffu] ^ (crc >> 8);
    return ~crc;
}

static FILE* pkg_fopen(const char* path, int write) {
#if defined(_WIN32)
    wchar_t wide[PKG_TAR_MAX_PATH];
    if (MultiByteToWideChar(CP_UTF8, 0, path, -1, wide, PKG_TAR_MAX_PATH) == 0) return NULL;
    return _wfopen(wide, write ? L"wb" : L"rb");
#else
    return fopen(path, write ? "wb" : "rb");
#endif
}

/* ---- gzip writer: stored deflate blocks ---- */
typedef struct {
    FILE* file;
    uint8_t block[65535];
    size_t used;
    uint32_t crc;
    uint32_t isize;
    int failed;
} PkgGz;

static void pkg_gz_put(PkgGz* gz, const void* data, size_t len) {
    if (!gz->failed && len && fwrite(data, 1, len, gz->file) != len) gz->failed = 1;
}

static void pkg_gz_flush_block(PkgGz* gz, int final_block) {
    uint8_t head[5];
    head[0] = final_block ? 1 : 0;
    head[1] = (uint8_t)(gz->used & 0xff);
    head[2] = (uint8_t)(gz->used >> 8);
    head[3] = (uint8_t)(~gz->used & 0xff);
    head[4] = (uint8_t)((~gz->used >> 8) & 0xff);
    pkg_gz_put(gz, head, 5);
    pkg_gz_put(gz, gz->block, gz->used);
    gz->used = 0;
}

static void pkg_gz_write(PkgGz* gz, const void* data, size_t len) {
    const uint8_t* p = (const uint8_t*)data;
    gz->crc = pkg_crc32_update(gz->crc, p, len);
    gz->isize += (uint32_t)len;
    while (len) {
        size_t room = sizeof(gz->block) - gz->used;
        size_t n = len < room ? len : room;
        memcpy(gz->block + gz->used, p, n);
        gz->used += n;
        p += n;
        len -= n;
        if (gz->used == sizeof(gz->block)) pkg_gz_flush_block(gz, 0);
    }
}

static void pkg_gz_begin(PkgGz* gz, FILE* file) {
    static const uint8_t header[10] = {0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff};
    memset(gz, 0, sizeof(*gz));
    gz->file = file;
    pkg_gz_put(gz, header, sizeof(header));
}

static int pkg_gz_finish(PkgGz* gz) {
    uint8_t tail[8];
    pkg_gz_flush_block(gz, 1);
    for (int i = 0; i < 4; i++) {
        tail[i] = (uint8_t)(gz->crc >> (8 * i));
        tail[4 + i] = (uint8_t)(gz->isize >> (8 * i));
    }
    pkg_gz_put(gz, tail, sizeof(tail));
    return gz->failed ? -1 : 0;
}

/* ---- ustar writer ---- */
static void pkg_tar_octal(char* field, size_t width, uint64_t value) {
    for (size_t i = width - 1; i-- > 0;) {
        field[i] = (char)('0' + (value & 7u));
        value >>= 3;
    }
    field[width - 1] = '\0';
}

static int pkg_tar_header(PkgGz* gz, const char* name, int is_dir, uint64_t size, uint32_t mode, uint64_t mtime) {
    uint8_t block[512];
    size_t name_len = strlen(name);
    const char* tail = name;
    memset(block, 0, sizeof(block));
    if (name_len > 100) {
        /* ustar: split at a '/' so prefix <= 155 and name <= 100. */
        size_t split = 0;
        for (size_t i = 0; i < name_len; i++) {
            if (name[i] == '/' && i <= 155 && name_len - i - 1 <= 100) split = i;
        }
        if (!split) return -1;
        tail = name + split + 1;
        name_len = strlen(tail);
        memcpy(block + 345, name, split);
    }
    memcpy(block, tail, name_len);
    pkg_tar_octal((char*)block + 100, 8, mode & 07777u);
    pkg_tar_octal((char*)block + 108, 8, 0);
    pkg_tar_octal((char*)block + 116, 8, 0);
    pkg_tar_octal((char*)block + 124, 12, is_dir ? 0 : size);
    pkg_tar_octal((char*)block + 136, 12, mtime);
    memset(block + 148, ' ', 8);
    block[156] = is_dir ? '5' : '0';
    memcpy(block + 257, "ustar", 6);
    memcpy(block + 263, "00", 2);
    uint32_t sum = 0;
    for (int i = 0; i < 512; i++) sum += block[i];
    pkg_tar_octal((char*)block + 148, 7, sum);
    block[155] = ' ';
    pkg_gz_write(gz, block, sizeof(block));
    return 0;
}

static int pkg_tar_add_file(PkgGz* gz, const char* full, const char* name, uint64_t size, uint32_t mode, uint64_t mtime) {
    if (size > 077777777777ULL) return -1;
    if (pkg_tar_header(gz, name, 0, size, mode, mtime) != 0) return -1;
    FILE* in = pkg_fopen(full, 0);
    if (!in) return -1;
    uint8_t buf[16384];
    uint64_t left = size;
    int rc = 0;
    while (left) {
        size_t want = left < sizeof(buf) ? (size_t)left : sizeof(buf);
        size_t got = fread(buf, 1, want, in);
        if (got != want) { rc = -1; break; }
        pkg_gz_write(gz, buf, got);
        left -= got;
    }
    fclose(in);
    if (rc != 0) return -1;
    size_t pad = (size_t)((512 - (size % 512)) % 512);
    if (pad) {
        uint8_t zeros[512] = {0};
        pkg_gz_write(gz, zeros, pad);
    }
    return 0;
}

static int pkg_tar_walk(PkgGz* gz, const char* dir, const char* rel, int depth) {
    if (depth > PKG_TAR_MAX_DEPTH) return -1;
#if defined(_WIN32)
    char pattern[PKG_TAR_MAX_PATH];
    wchar_t wide[PKG_TAR_MAX_PATH];
    if (snprintf(pattern, sizeof(pattern), "%s/*", dir) >= (int)sizeof(pattern)) return -1;
    if (MultiByteToWideChar(CP_UTF8, 0, pattern, -1, wide, PKG_TAR_MAX_PATH) == 0) return -1;
    WIN32_FIND_DATAW find;
    HANDLE handle = FindFirstFileW(wide, &find);
    if (handle == INVALID_HANDLE_VALUE) return GetLastError() == ERROR_FILE_NOT_FOUND ? 0 : -1;
    int rc = 0;
    do {
        char entry[1024];
        if (find.cFileName[0] == L'.' && (find.cFileName[1] == 0 || (find.cFileName[1] == L'.' && find.cFileName[2] == 0))) continue;
        if (WideCharToMultiByte(CP_UTF8, 0, find.cFileName, -1, entry, sizeof(entry), NULL, NULL) == 0) { rc = -1; break; }
        char full[PKG_TAR_MAX_PATH], name[PKG_TAR_MAX_PATH];
        if (snprintf(full, sizeof(full), "%s/%s", dir, entry) >= (int)sizeof(full)) { rc = -1; break; }
        if (snprintf(name, sizeof(name), "%s%s%s", rel, rel[0] ? "/" : "", entry) >= (int)sizeof(name)) { rc = -1; break; }
        int is_dir = (find.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) != 0;
        uint64_t size = ((uint64_t)find.nFileSizeHigh << 32) | find.nFileSizeLow;
        if (is_dir) {
            if (pkg_tar_header(gz, name, 1, 0, 0755, 0) != 0 || pkg_tar_walk(gz, full, name, depth + 1) != 0) { rc = -1; break; }
        } else if (pkg_tar_add_file(gz, full, name, size, 0644, 0) != 0) { rc = -1; break; }
    } while (FindNextFileW(handle, &find));
    FindClose(handle);
    return rc;
#else
    DIR* d = opendir(dir);
    if (!d) return -1;
    int rc = 0;
    struct dirent* e;
    while ((e = readdir(d)) != NULL) {
        if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
        char full[PKG_TAR_MAX_PATH], name[PKG_TAR_MAX_PATH];
        if (snprintf(full, sizeof(full), "%s/%s", dir, e->d_name) >= (int)sizeof(full)) { rc = -1; break; }
        if (snprintf(name, sizeof(name), "%s%s%s", rel, rel[0] ? "/" : "", e->d_name) >= (int)sizeof(name)) { rc = -1; break; }
        struct stat st;
        if (stat(full, &st) != 0) { rc = -1; break; }
        if (S_ISDIR(st.st_mode)) {
            if (pkg_tar_header(gz, name, 1, 0, (uint32_t)st.st_mode & 0777, (uint64_t)st.st_mtime) != 0 ||
                pkg_tar_walk(gz, full, name, depth + 1) != 0) { rc = -1; break; }
        } else if (S_ISREG(st.st_mode)) {
            if (pkg_tar_add_file(gz, full, name, (uint64_t)st.st_size, (uint32_t)st.st_mode & 0777, (uint64_t)st.st_mtime) != 0) { rc = -1; break; }
        }
    }
    closedir(d);
    return rc;
#endif
}

int32_t rt_package_create_tarball(const uint8_t* src, uint64_t src_len,
                                  const uint8_t* out, uint64_t out_len) {
    if (!src || !out || src_len == 0 || out_len == 0 || src_len >= PKG_TAR_MAX_PATH || out_len >= PKG_TAR_MAX_PATH) return -1;
    char src_path[PKG_TAR_MAX_PATH], out_path[PKG_TAR_MAX_PATH];
    memcpy(src_path, src, (size_t)src_len);
    src_path[src_len] = '\0';
    memcpy(out_path, out, (size_t)out_len);
    out_path[out_len] = '\0';
    FILE* file = pkg_fopen(out_path, 1);
    if (!file) return -1;
    PkgGz* gz = (PkgGz*)malloc(sizeof(PkgGz));
    if (!gz) { fclose(file); return -1; }
    pkg_gz_begin(gz, file);
    int rc = pkg_tar_walk(gz, src_path, "", 0);
    if (rc == 0) {
        uint8_t zeros[1024] = {0};
        pkg_gz_write(gz, zeros, sizeof(zeros));
        rc = pkg_gz_finish(gz);
    }
    free(gz);
    if (fclose(file) != 0) rc = -1;
    return rc == 0 ? 0 : -1;
}

/* ---- inflate (RFC 1951), canonical-Huffman decode ---- */
typedef struct {
    const uint8_t* in;
    size_t in_len, in_pos;
    uint32_t bit_buf;
    int bit_cnt;
    uint8_t* out;
    size_t out_len, out_cap;
    int error;
} PkgInf;

typedef struct { uint16_t count[16]; uint16_t symbol[288]; } PkgHuff;

static int pkg_inf_bits(PkgInf* s, int need) {
    while (s->bit_cnt < need) {
        if (s->in_pos >= s->in_len) { s->error = 1; return 0; }
        s->bit_buf |= (uint32_t)s->in[s->in_pos++] << s->bit_cnt;
        s->bit_cnt += 8;
    }
    int v = (int)(s->bit_buf & ((1u << need) - 1u));
    s->bit_buf >>= need;
    s->bit_cnt -= need;
    return v;
}

static void pkg_inf_put(PkgInf* s, uint8_t b) {
    if (s->out_len == s->out_cap) {
        size_t cap = s->out_cap ? s->out_cap * 2 : 65536;
        uint8_t* grown = (uint8_t*)realloc(s->out, cap);
        if (!grown) { s->error = 1; return; }
        s->out = grown;
        s->out_cap = cap;
    }
    s->out[s->out_len++] = b;
}

static int pkg_huff_build(PkgHuff* h, const uint16_t* lengths, int n) {
    uint16_t offs[16];
    memset(h->count, 0, sizeof(h->count));
    memset(h->symbol, 0, sizeof(h->symbol));
    for (int i = 0; i < n; i++) h->count[lengths[i]]++;
    if (h->count[0] == n) return 0;
    int left = 1;
    for (int len = 1; len < 16; len++) {
        left <<= 1;
        left -= h->count[len];
        if (left < 0) return -1;
    }
    offs[1] = 0;
    for (int len = 1; len < 15; len++) offs[len + 1] = (uint16_t)(offs[len] + h->count[len]);
    for (int i = 0; i < n; i++) if (lengths[i]) h->symbol[offs[lengths[i]]++] = (uint16_t)i;
    return 0;
}

static int pkg_huff_decode(PkgInf* s, const PkgHuff* h) {
    int code = 0, first = 0, index = 0;
    for (int len = 1; len < 16; len++) {
        code |= pkg_inf_bits(s, 1);
        if (s->error) return -1;
        int count = h->count[len];
        if (code - count < first) return h->symbol[index + (code - first)];
        index += count;
        first += count;
        first <<= 1;
        code <<= 1;
    }
    s->error = 1;
    return -1;
}

static void pkg_inf_codes(PkgInf* s, const PkgHuff* lit, const PkgHuff* dist) {
    static const uint16_t len_base[29] = {3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258};
    static const uint16_t len_extra[29] = {0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0};
    static const uint16_t dist_base[30] = {1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577};
    static const uint16_t dist_extra[30] = {0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13};
    for (;;) {
        int sym = pkg_huff_decode(s, lit);
        if (s->error) return;
        if (sym < 256) { pkg_inf_put(s, (uint8_t)sym); if (s->error) return; continue; }
        if (sym == 256) return;
        sym -= 257;
        if (sym >= 29) { s->error = 1; return; }
        int len = len_base[sym] + pkg_inf_bits(s, len_extra[sym]);
        int ds = pkg_huff_decode(s, dist);
        if (s->error || ds < 0 || ds >= 30) { s->error = 1; return; }
        size_t d = (size_t)dist_base[ds] + (size_t)pkg_inf_bits(s, dist_extra[ds]);
        if (s->error || d > s->out_len) { s->error = 1; return; }
        for (int i = 0; i < len; i++) { pkg_inf_put(s, s->out[s->out_len - d]); if (s->error) return; }
    }
}

static void pkg_inflate(PkgInf* s) {
    int final_block;
    do {
        final_block = pkg_inf_bits(s, 1);
        int type = pkg_inf_bits(s, 2);
        if (s->error) return;
        if (type == 0) {
            s->bit_buf = 0;
            s->bit_cnt = 0;
            if (s->in_pos + 4 > s->in_len) { s->error = 1; return; }
            unsigned len = (unsigned)s->in[s->in_pos] | ((unsigned)s->in[s->in_pos + 1] << 8);
            unsigned nlen = (unsigned)s->in[s->in_pos + 2] | ((unsigned)s->in[s->in_pos + 3] << 8);
            s->in_pos += 4;
            if (len != (~nlen & 0xffffu) || s->in_pos + len > s->in_len) { s->error = 1; return; }
            for (unsigned i = 0; i < len; i++) { pkg_inf_put(s, s->in[s->in_pos++]); if (s->error) return; }
        } else if (type == 1) {
            PkgHuff lit, dist;
            uint16_t lengths[288];
            int i = 0;
            for (; i < 144; i++) lengths[i] = 8;
            for (; i < 256; i++) lengths[i] = 9;
            for (; i < 280; i++) lengths[i] = 7;
            for (; i < 288; i++) lengths[i] = 8;
            pkg_huff_build(&lit, lengths, 288);
            for (i = 0; i < 30; i++) lengths[i] = 5;
            pkg_huff_build(&dist, lengths, 30);
            pkg_inf_codes(s, &lit, &dist);
        } else if (type == 2) {
            static const uint8_t order[19] = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15};
            uint16_t lengths[320];
            int nlen = pkg_inf_bits(s, 5) + 257;
            int ndist = pkg_inf_bits(s, 5) + 1;
            int ncode = pkg_inf_bits(s, 4) + 4;
            if (s->error || nlen > 286 || ndist > 30) { s->error = 1; return; }
            int i = 0;
            for (; i < ncode; i++) lengths[order[i]] = (uint16_t)pkg_inf_bits(s, 3);
            for (; i < 19; i++) lengths[order[i]] = 0;
            PkgHuff lencode, lit, dist;
            if (s->error || pkg_huff_build(&lencode, lengths, 19) != 0) { s->error = 1; return; }
            int idx = 0;
            while (idx < nlen + ndist) {
                int sym = pkg_huff_decode(s, &lencode);
                if (s->error) return;
                if (sym < 16) { lengths[idx++] = (uint16_t)sym; continue; }
                int prev = 0, rep;
                if (sym == 16) {
                    if (idx == 0) { s->error = 1; return; }
                    prev = lengths[idx - 1];
                    rep = 3 + pkg_inf_bits(s, 2);
                } else if (sym == 17) rep = 3 + pkg_inf_bits(s, 3);
                else rep = 11 + pkg_inf_bits(s, 7);
                if (s->error || idx + rep > nlen + ndist) { s->error = 1; return; }
                while (rep--) lengths[idx++] = (uint16_t)prev;
            }
            if (lengths[256] == 0) { s->error = 1; return; }
            if (pkg_huff_build(&lit, lengths, nlen) < 0 || pkg_huff_build(&dist, lengths + nlen, ndist) < 0) { s->error = 1; return; }
            pkg_inf_codes(s, &lit, &dist);
        } else {
            s->error = 1;
            return;
        }
    } while (!final_block && !s->error);
}

/* Returns a malloc'd tar byte stream, or NULL on any gzip/deflate error. */
static uint8_t* pkg_gunzip_file(const char* path, size_t* out_len) {
    FILE* f = pkg_fopen(path, 0);
    if (!f) return NULL;
    size_t cap = 0, len = 0;
    uint8_t* data = NULL;
    for (;;) {
        if (len == cap) {
            size_t ncap = cap ? cap * 2 : 65536;
            uint8_t* grown = (uint8_t*)realloc(data, ncap);
            if (!grown) { free(data); fclose(f); return NULL; }
            data = grown;
            cap = ncap;
        }
        size_t got = fread(data + len, 1, cap - len, f);
        len += got;
        if (got == 0) break;
    }
    fclose(f);
    if (len < 18 || data[0] != 0x1f || data[1] != 0x8b || data[2] != 8) { free(data); return NULL; }
    size_t pos = 10;
    uint8_t flg = data[3];
    if (flg & 4) { pos += 2 + (data[pos] | (data[pos + 1] << 8)); }
    if (flg & 8) { while (pos < len && data[pos]) pos++; pos++; }
    if (flg & 16) { while (pos < len && data[pos]) pos++; pos++; }
    if (flg & 2) pos += 2;
    if (pos + 8 > len) { free(data); return NULL; }
    PkgInf s;
    memset(&s, 0, sizeof(s));
    s.in = data + pos;
    s.in_len = len - pos - 8;
    pkg_inflate(&s);
    if (s.error) { free(s.out); free(data); return NULL; }
    const uint8_t* tail = data + len - 8;
    uint32_t want_crc = rt__shared_read_u32_le(tail);
    uint32_t want_size = rt__shared_read_u32_le(tail + 4);
    if (pkg_crc32_update(0, s.out, s.out_len) != want_crc || (uint32_t)s.out_len != want_size) {
        free(s.out);
        free(data);
        return NULL;
    }
    free(data);
    *out_len = s.out_len;
    return s.out ? s.out : (uint8_t*)calloc(1, 1);
}

static int pkg_tar_name_safe(const char* name) {
    if (!name[0] || name[0] == '/' || strchr(name, '\\') || strchr(name, ':')) return 0;
    for (const char* p = name; *p;) {
        const char* end = strchr(p, '/');
        size_t n = end ? (size_t)(end - p) : strlen(p);
        if (n == 2 && p[0] == '.' && p[1] == '.') return 0;
        p = end ? end + 1 : p + n;
    }
    return 1;
}

static uint64_t pkg_tar_parse_octal(const uint8_t* field, size_t width) {
    uint64_t v = 0;
    for (size_t i = 0; i < width && field[i] >= '0' && field[i] <= '7'; i++) v = (v << 3) | (uint64_t)(field[i] - '0');
    return v;
}

static int pkg_mkdir_c(const char* path) {
    return rt_dir_create_all((const uint8_t*)path, (uint64_t)strlen(path)) ? 0 : -1;
}

int32_t rt_package_extract_tarball(const uint8_t* tarball, uint64_t tarball_len,
                                   const uint8_t* dest, uint64_t dest_len) {
    if (!tarball || !dest || tarball_len == 0 || dest_len == 0 || tarball_len >= PKG_TAR_MAX_PATH || dest_len >= PKG_TAR_MAX_PATH) return -1;
    char tar_path[PKG_TAR_MAX_PATH], dest_path[PKG_TAR_MAX_PATH];
    memcpy(tar_path, tarball, (size_t)tarball_len);
    tar_path[tarball_len] = '\0';
    memcpy(dest_path, dest, (size_t)dest_len);
    dest_path[dest_len] = '\0';
    size_t tar_len = 0;
    uint8_t* tar = pkg_gunzip_file(tar_path, &tar_len);
    if (!tar) return -1;
    int rc = pkg_mkdir_c(dest_path);
    char long_name[PKG_TAR_MAX_PATH];
    int have_long = 0;
    size_t pos = 0;
    while (rc == 0 && pos + 512 <= tar_len) {
        const uint8_t* h = tar + pos;
        int zero = 1;
        for (int i = 0; i < 512 && zero; i++) if (h[i]) zero = 0;
        if (zero) break;
        uint64_t size = pkg_tar_parse_octal(h + 124, 12);
        size_t data_pos = pos + 512;
        if (size > tar_len || data_pos + size > tar_len) { rc = -1; break; }
        size_t next = data_pos + (size_t)((size + 511) / 512) * 512;
        char type = (char)h[156];
        if (type == 'L') {
            if (size >= sizeof(long_name)) { rc = -1; break; }
            memcpy(long_name, tar + data_pos, (size_t)size);
            long_name[size] = '\0';
            have_long = 1;
            pos = next;
            continue;
        }
        if (type == 'x' || type == 'g') { pos = next; continue; }
        char name[PKG_TAR_MAX_PATH];
        if (have_long) {
            snprintf(name, sizeof(name), "%s", long_name);
            have_long = 0;
        } else {
            char part[156], base[101];
            memcpy(base, h, 100);
            base[100] = '\0';
            memcpy(part, h + 345, 155);
            part[155] = '\0';
            if (part[0]) snprintf(name, sizeof(name), "%s/%s", part, base);
            else snprintf(name, sizeof(name), "%s", base);
        }
        size_t n = strlen(name);
        while (n && name[n - 1] == '/') name[--n] = '\0';
        if (n >= 2 && name[0] == '.' && name[1] == '/') memmove(name, name + 2, strlen(name + 2) + 1);
        if (!strcmp(name, ".") || !name[0]) { pos = next; continue; }
        if (!pkg_tar_name_safe(name)) { rc = -1; break; }
        char full[PKG_TAR_MAX_PATH];
        if (snprintf(full, sizeof(full), "%s/%s", dest_path, name) >= (int)sizeof(full)) { rc = -1; break; }
        if (type == '5') {
            rc = pkg_mkdir_c(full);
        } else if (type == '0' || type == '\0') {
            char parent[PKG_TAR_MAX_PATH];
            snprintf(parent, sizeof(parent), "%s", full);
            char* slash = strrchr(parent, '/');
            if (slash) { *slash = '\0'; rc = pkg_mkdir_c(parent); }
            FILE* f = rc == 0 ? pkg_fopen(full, 1) : NULL;
            if (!f) { rc = -1; break; }
            if (size && fwrite(tar + data_pos, 1, (size_t)size, f) != (size_t)size) rc = -1;
            if (fclose(f) != 0) rc = -1;
#if !defined(_WIN32)
            if (rc == 0) chmod(full, (mode_t)(pkg_tar_parse_octal(h + 100, 8) & 0777));
#endif
        } else {
            fprintf(stderr, "Runtime error: rt_package_extract_tarball: unsupported tar entry type 0x%02x for %s\n", (unsigned)(uint8_t)type, name);
            rc = -1;
        }
        pos = next;
    }
    free(tar);
    return rc == 0 ? 0 : -1;
}

/* ================================================================
 * Wall-clock, calendar, and system singles for the sffi/system externs
 * (src/lib/nogc_sync_mut/sffi/system.spl, io/time_ops.spl).
 *
 * These 18 names previously existed only as interpreter shims (and 17 of
 * them not even there), so every native link left them unresolved -- the
 * Stage 2 Windows link failed on exactly this set. See
 * doc/08_tracking/bug/stage2_windows_unresolved_inventory_2026-08-31.md
 * group D plus the rt_cpu_count / rt_uuid_v4 singles of group I.
 *
 * Unit contract (pinned here because some functions have zero in-tree
 * callers and the .spl doc comments are the only other contract):
 *   - rt_time_now                : whole SECONDS since the Unix epoch (UTC).
 *   - rt_time_now_unix_millis,
 *     rt_time_millis             : WALL-CLOCK milliseconds since the epoch.
 *     (system.spl calls rt_time_millis "monotonic or wall-clock"; wall is
 *     chosen so it agrees with rt_time_ms / rt_time_now_unix_millis.)
 *   - rt_timestamp_*             : MICROSECONDS since the Unix epoch, the
 *     same unit as rt_timestamp_get_* / the calendar oracle.
 *   - rt_time_format             : ts is whole SECONDS since the epoch.
 *   - rt_time_year..second       : LOCAL time components of now.
 *
 * Calendar arithmetic is pure integer civil-calendar math copied from
 * src/runtime/test/runtime_timestamp_calendar_oracle.c so the results agree
 * with rt_timestamp_get_* on every platform, including pre-1970 values that
 * Windows CRT gmtime/_mkgmtime reject. Only the local-time family touches
 * the CRT (localtime_s / localtime_r).
 *
 * `text` ABI: none of these names appear in text_arg_indices
 * (src/compiler/50.mir/text_extern_abi.spl), so a text argument arrives as a
 * single tagged runtime value (decode via rt_string_data / rt_string_len)
 * and a text return is a tagged value built by rt_string_new -- the
 * rt_shell_exec convention. Failure returns for text-returning functions are
 * the empty string, per the facade's "empty text is failure" contracts.
 * ================================================================ */

#include <stdio.h>
#include <time.h>
#if !defined(_WIN32)
#include <fcntl.h>
#endif

static int64_t core_host_floor_div(int64_t value, int64_t divisor) {
    int64_t quotient = value / divisor;
    if ((value % divisor) != 0 && ((value < 0) != (divisor < 0))) quotient--;
    return quotient;
}

/* Civil-calendar conversions (Howard Hinnant's algorithms, same source as
 * runtime_timestamp_calendar_oracle.c -- keep result-compatible with it). */
static void core_host_days_to_ymd(int64_t z, int64_t* year, int64_t* month, int64_t* day) {
    z += 719468;
    int64_t era = (z >= 0 ? z : z - 146096) / 146097;
    int64_t doe = z - era * 146097;
    int64_t yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    int64_t y = yoe + era * 400;
    int64_t doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    int64_t mp = (5 * doy + 2) / 153;
    int64_t d = doy - (153 * mp + 2) / 5 + 1;
    int64_t m = mp < 10 ? mp + 3 : mp - 9;
    y += (m <= 2);
    *year = y;
    *month = m;
    *day = d;
}

static int64_t core_host_ymd_to_days(int64_t year, int64_t month, int64_t day) {
    int64_t y = year - (month <= 2 ? 1 : 0);
    int64_t m = month + (month <= 2 ? 9 : -3);
    int64_t era = (y >= 0 ? y : y - 399) / 400;
    int64_t yoe = y - era * 400;
    int64_t doy = (153 * m + 2) / 5 + day - 1;
    int64_t doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + doe - 719468;
}

typedef struct {
    int64_t year, month, day, hour, minute, second, microsecond;
} CoreHostCivilTime;

static void core_host_micros_to_civil(int64_t micros, CoreHostCivilTime* out) {
    int64_t days = core_host_floor_div(micros, 86400000000LL);
    int64_t tod = micros - days * 86400000000LL; /* 0..86399999999 */
    core_host_days_to_ymd(days, &out->year, &out->month, &out->day);
    out->hour = tod / 3600000000LL;
    out->minute = (tod / 60000000LL) % 60;
    out->second = (tod / 1000000LL) % 60;
    out->microsecond = tod % 1000000LL;
}


/* Snapshot links use tagged text so their extern ABI needs no raw-text MIR
 * exception. All paths here are private absolute paths emitted by the snapshot
 * owner; the native boundary still rejects NUL, dot components and escapes. */
static int core_snapshot_text(int64_t value, char* out, size_t size) {
    int64_t len = rt_string_len(value);
    const uint8_t* data = rt_string_data(value);
    if (len <= 0 || (uint64_t)len >= size || !data ||
        memchr(data, 0, (size_t)len)) return 0;
    memcpy(out, data, (size_t)len);
    out[len] = '\0';
    return 1;
}

static int core_snapshot_absolute(const char* path) {
    size_t len = strlen(path);
    if (len < 2 || len >= 4096 || path[len - 1] == '/' || strchr(path, '\\')) return 0;
#if defined(_WIN32)
    if (!((path[0] >= 'A' && path[0] <= 'Z') ||
          (path[0] >= 'a' && path[0] <= 'z')) || path[1] != ':' || path[2] != '/') return 0;
    size_t start = 3;
#else
    if (path[0] != '/') return 0;
    size_t start = 1;
#endif
    for (size_t i = start; i < len;) {
        size_t next = i;
        while (next < len && path[next] != '/') next++;
        size_t n = next - i;
        if (!n || (n == 1 && path[i] == '.') ||
            (n == 2 && path[i] == '.' && path[i + 1] == '.')) return 0;
        i = next + 1;
    }
    return 1;
}

/* Resolve the raw relative target lexically, including bounded '..'. A
 * filesystem walk below checks every resolved component without following a
 * symlink. Link text is left untouched for exact readback. */
static int core_snapshot_target(const char* root, const char* link,
                                const char* target, char resolved[4096]) {
    size_t root_len = strlen(root), link_len = strlen(link), target_len = strlen(target);
    if (!core_snapshot_absolute(root) || !core_snapshot_absolute(link) ||
        link_len <= root_len + 1 || strncmp(link, root, root_len) != 0 ||
        link[root_len] != '/' || !target_len || target_len >= 4096 ||
        target[0] == '/' || strchr(target, '\\') || strchr(target, ':') ||
        target[target_len - 1] == '/') return 0;
    const char* leaf = strrchr(link, '/');
    if (!leaf || !leaf[1]) return 0;
    size_t used = (size_t)(leaf - link);
    if (used < root_len) return 0;
    memcpy(resolved, link, used);
    resolved[used] = '\0';
    for (size_t i = 0; i < target_len;) {
        size_t next = i;
        while (next < target_len && target[next] != '/') next++;
        size_t n = next - i;
        if (n == 0) return 0;
        if (n == 1 && target[i] == '.') {
            /* no change */
        } else if (n == 2 && target[i] == '.' && target[i + 1] == '.') {
            if (used == root_len) return 0;
            const char* previous = strrchr(resolved, '/');
            if (!previous || (size_t)(previous - resolved) < root_len) return 0;
            used = (size_t)(previous - resolved);
            resolved[used] = '\0';
        } else {
            if (used + 1 + n >= 4096) return 0;
            resolved[used++] = '/';
            memcpy(resolved + used, target + i, n);
            used += n;
            resolved[used] = '\0';
        }
        i = next + 1;
    }
    return core_snapshot_absolute(resolved);
}

#if defined(_WIN32)
static int core_snapshot_windows_target_kind(const char* path, int32_t kind) {
    wchar_t* wide = rt_win_long_path_widen(path);
    if (!wide) return 0;
    int real = rt_win_profile_path_parents_are_real(wide);
    DWORD attrs = real ? GetFileAttributesW(wide) : INVALID_FILE_ATTRIBUTES;
    free(wide);
    return attrs != INVALID_FILE_ATTRIBUTES &&
        (attrs & FILE_ATTRIBUTE_REPARSE_POINT) == 0 &&
        ((kind == 2 && (attrs & FILE_ATTRIBUTE_DIRECTORY) != 0) ||
         (kind == 1 && (attrs & FILE_ATTRIBUTE_DIRECTORY) == 0 &&
          (attrs & FILE_ATTRIBUTE_DEVICE) == 0));
}

static wchar_t* core_snapshot_windows_raw_target(const char* target) {
    return spl_win_utf8_to_wide(target, -1, MB_ERR_INVALID_CHARS, malloc, free, NULL);
}

static int core_snapshot_windows_match(const char* link, const char* target,
                                       int32_t kind) {
    wchar_t* wide = rt_win_long_path_widen(link);
    if (!wide) return 0;
    if (!rt_win_profile_path_parents_are_real(wide)) { free(wide); return 0; }
    HANDLE handle = CreateFileW(wide, FILE_READ_ATTRIBUTES,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL, OPEN_EXISTING,
        FILE_FLAG_OPEN_REPARSE_POINT | FILE_FLAG_BACKUP_SEMANTICS, NULL);
    free(wide);
    if (handle == INVALID_HANDLE_VALUE) return 0;
    BY_HANDLE_FILE_INFORMATION info;
    BYTE bytes[MAXIMUM_REPARSE_DATA_BUFFER_SIZE];
    DWORD returned = 0;
    int ok = GetFileInformationByHandle(handle, &info) &&
        (info.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT) != 0 &&
        ((kind == 2 && (info.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) != 0) ||
         (kind == 1 && (info.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0)) &&
        DeviceIoControl(handle, FSCTL_GET_REPARSE_POINT, NULL, 0, bytes,
            (DWORD)sizeof(bytes), &returned, NULL);
    CloseHandle(handle);
    /* MinGW does not publish REPARSE_DATA_BUFFER. The symlink wire layout is
     * 8-byte header, four USHORT offsets/lengths, ULONG flags, UTF-16 path. */
    if (!ok || returned < 20) return 0;
    DWORD tag = 0, flags = 0;
    USHORT wire_length = 0, offset = 0, length = 0;
    memcpy(&tag, bytes, sizeof(tag));
    memcpy(&wire_length, bytes + 4, sizeof(wire_length));
    memcpy(&offset, bytes + 12, sizeof(offset));
    memcpy(&length, bytes + 14, sizeof(length));
    memcpy(&flags, bytes + 16, sizeof(flags));
    if (tag != IO_REPARSE_TAG_SYMLINK || (flags & SYMLINK_FLAG_RELATIVE) == 0 ||
        (size_t)wire_length + 8 > returned || (offset & 1) || (length & 1) ||
        20u + (size_t)offset + length > returned ||
        20u + (size_t)offset + length > (size_t)wire_length + 8 ||
        length > 8192) return 0;
    WCHAR raw[4096];
    memcpy(raw, bytes + 20 + offset, length);
    char text[4096];
    int count = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, raw,
        length / (USHORT)sizeof(WCHAR), text, (int)sizeof(text), NULL, NULL);
    return count > 0 && (size_t)count == strlen(target) &&
        memcmp(text, target, (size_t)count) == 0;
}
#else
static int core_snapshot_posix_parent(const char* path, char leaf[4096]) {
    if (!core_snapshot_absolute(path)) return -1;
    int fd = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) return -1;
    const char* part = path + 1;
    while (*part) {
        const char* slash = strchr(part, '/');
        size_t n = slash ? (size_t)(slash - part) : strlen(part);
        if (!n || n >= 4096) { close(fd); return -1; }
        memcpy(leaf, part, n);
        leaf[n] = '\0';
        if (!slash) return fd;
        int next = openat(fd, leaf, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        close(fd);
        if (next < 0) return -1;
        fd = next;
        part = slash + 1;
    }
    close(fd);
    return -1;
}

static int core_snapshot_posix_target_kind(const char* path, int32_t kind) {
    char leaf[4096];
    int parent = core_snapshot_posix_parent(path, leaf);
    if (parent < 0) return 0;
    struct stat info;
    int ok = fstatat(parent, leaf, &info, AT_SYMLINK_NOFOLLOW) == 0 &&
        ((kind == 1 && S_ISREG(info.st_mode)) || (kind == 2 && S_ISDIR(info.st_mode)));
    close(parent);
    return ok;
}

static int core_snapshot_posix_match(const char* link, const char* target) {
    char leaf[4096], raw[4096];
    int parent = core_snapshot_posix_parent(link, leaf);
    if (parent < 0) return 0;
    struct stat info;
    ssize_t length = readlinkat(parent, leaf, raw, sizeof(raw));
    int ok = fstatat(parent, leaf, &info, AT_SYMLINK_NOFOLLOW) == 0 &&
        S_ISLNK(info.st_mode) && length >= 0 &&
        (size_t)length == strlen(target) && memcmp(raw, target, (size_t)length) == 0;
    close(parent);
    return ok;
}
#endif

int32_t rt_snapshot_symlink_match_nofollow_v1(int64_t root_value,
        int64_t link_value, int64_t target_value, int32_t kind) {
    char root[4096], link[4096], target[4096], resolved[4096];
    if ((kind != 1 && kind != 2) ||
        !core_snapshot_text(root_value, root, sizeof(root)) ||
        !core_snapshot_text(link_value, link, sizeof(link)) ||
        !core_snapshot_text(target_value, target, sizeof(target)) ||
        !core_snapshot_target(root, link, target, resolved)) return -1;
#if defined(_WIN32)
    return core_snapshot_windows_target_kind(resolved, kind) &&
        core_snapshot_windows_match(link, target, kind) ? 0 : -1;
#else
    return core_snapshot_posix_target_kind(resolved, kind) &&
        core_snapshot_posix_match(link, target) ? 0 : -1;
#endif
}

int32_t rt_snapshot_symlink_create_nofollow_v1(int64_t root_value,
        int64_t link_value, int64_t target_value, int32_t kind) {
    char root[4096], link[4096], target[4096], resolved[4096];
    if ((kind != 1 && kind != 2) ||
        !core_snapshot_text(root_value, root, sizeof(root)) ||
        !core_snapshot_text(link_value, link, sizeof(link)) ||
        !core_snapshot_text(target_value, target, sizeof(target)) ||
        !core_snapshot_target(root, link, target, resolved)) return -1;
#if defined(_WIN32)
    if (!core_snapshot_windows_target_kind(resolved, kind)) return -1;
    wchar_t* wide_link = rt_win_long_path_widen(link);
    wchar_t* wide_target = core_snapshot_windows_raw_target(target);
    if (!wide_link || !wide_target) { free(wide_link); free(wide_target); return -1; }
    if (!rt_win_profile_path_parents_are_real(wide_link) ||
        GetFileAttributesW(wide_link) != INVALID_FILE_ATTRIBUTES) {
        free(wide_link); free(wide_target); return -1;
    }
    DWORD flags = kind == 2 ? SYMBOLIC_LINK_FLAG_DIRECTORY : 0;
    BOOLEAN created = CreateSymbolicLinkW(wide_link, wide_target, flags | 0x2u);
    if (!created && GetLastError() == ERROR_INVALID_PARAMETER)
        created = CreateSymbolicLinkW(wide_link, wide_target, flags);
    free(wide_link); free(wide_target);
    if (!created) return -1;
#else
    if (!core_snapshot_posix_target_kind(resolved, kind)) return -1;
    char leaf[4096];
    int parent = core_snapshot_posix_parent(link, leaf);
    if (parent < 0) return -1;
    int created = symlinkat(target, parent, leaf) == 0;
    close(parent);
    if (!created) return -1;
#endif
    return rt_snapshot_symlink_match_nofollow_v1(root_value, link_value,
        target_value, kind);
}

int32_t rt_snapshot_readonly_nofollow_v1(int64_t path_value, int32_t kind) {
    char path[4096];
    if ((kind != 1 && kind != 2) ||
        !core_snapshot_text(path_value, path, sizeof(path)) ||
        !core_snapshot_absolute(path)) return -1;
#if defined(_WIN32)
    /* DIRECTORY READONLY is ignored for child creation by Windows. Returning
     * success there would invent a physical seal, so only files are supported. */
    if (kind != 1) return -1;
    wchar_t* wide = rt_win_long_path_widen(path);
    if (!wide) return -1;
    if (!rt_win_profile_path_parents_are_real(wide)) { free(wide); return -1; }
    HANDLE handle = CreateFileW(wide, FILE_READ_ATTRIBUTES | FILE_WRITE_ATTRIBUTES,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL, OPEN_EXISTING,
        FILE_FLAG_OPEN_REPARSE_POINT, NULL);
    free(wide);
    if (handle == INVALID_HANDLE_VALUE) return -1;
    FILE_BASIC_INFO info;
    int ok = GetFileInformationByHandleEx(handle, FileBasicInfo, &info, sizeof(info)) &&
        (info.FileAttributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT |
                                FILE_ATTRIBUTE_DEVICE)) == 0;
    if (ok) {
        info.FileAttributes |= FILE_ATTRIBUTE_READONLY;
        ok = SetFileInformationByHandle(handle, FileBasicInfo, &info, sizeof(info)) &&
            GetFileInformationByHandleEx(handle, FileBasicInfo, &info, sizeof(info)) &&
            (info.FileAttributes & FILE_ATTRIBUTE_READONLY) != 0 &&
            (info.FileAttributes & FILE_ATTRIBUTE_REPARSE_POINT) == 0;
    }
    CloseHandle(handle);
    return ok ? 0 : -1;
#else
    char leaf[4096];
    int parent = core_snapshot_posix_parent(path, leaf);
    if (parent < 0) return -1;
    int fd = openat(parent, leaf, O_RDONLY | O_NOFOLLOW | O_CLOEXEC |
        (kind == 2 ? O_DIRECTORY : 0));
    close(parent);
    if (fd < 0) return -1;
    struct stat before, after;
    int ok = fstat(fd, &before) == 0 &&
        ((kind == 1 && S_ISREG(before.st_mode)) ||
         (kind == 2 && S_ISDIR(before.st_mode)));
    mode_t desired = ok ? before.st_mode & (mode_t)07777 & ~(mode_t)0222 : 0;
    if (ok) ok = fchmod(fd, desired) == 0 && fstat(fd, &after) == 0 &&
                 (after.st_mode & 0222) == 0;
    close(fd);
    return ok ? 0 : -1;
#endif
}

static int64_t core_host_text_result(const char* s) {
    if (!s) return rt_string_new(NULL, 0);
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

/* ---- Wall clock ---- */

int64_t rt_time_now(void) {
    int64_t micros = rt_time_now_unix_micros();
    return micros < 0 ? -1 : core_host_floor_div(micros, 1000000LL);
}

int64_t rt_time_now_unix_millis(void) {
    int64_t micros = rt_time_now_unix_micros();
    return micros < 0 ? -1 : core_host_floor_div(micros, 1000LL);
}

int64_t rt_time_millis(void) {
    return rt_time_now_unix_millis();
}

/* ---- Local-time components of now (-1 on clock/CRT failure) ---- */

static int core_host_local_now(struct tm* out) {
    time_t now = time(NULL);
    if (now == (time_t)-1) return 0;
#if defined(_WIN32)
    return localtime_s(out, &now) == 0;
#else
    return localtime_r(&now, out) != NULL;
#endif
}

int64_t rt_time_year(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_year + 1900 : -1;
}
int64_t rt_time_month(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_mon + 1 : -1;
}
int64_t rt_time_day(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_mday : -1;
}
int64_t rt_time_hour(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_hour : -1;
}
int64_t rt_time_minute(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_min : -1;
}
int64_t rt_time_second(void) {
    struct tm t;
    return core_host_local_now(&t) ? (int64_t)t.tm_sec : -1;
}

/* ---- Timestamp (micros) -> text ---- */

static void core_host_format_civil(const CoreHostCivilTime* ct, char sep,
                                   int with_zone, char* buf, size_t buf_size) {
    size_t used = (size_t)snprintf(buf, buf_size,
        "%04lld-%02lld-%02lld%c%02lld:%02lld:%02lld",
        (long long)ct->year, (long long)ct->month, (long long)ct->day, sep,
        (long long)ct->hour, (long long)ct->minute, (long long)ct->second);
    if (used >= buf_size) return;
    if (ct->microsecond != 0) {
        used += (size_t)snprintf(buf + used, buf_size - used, ".%06lld",
                                 (long long)ct->microsecond);
        if (used >= buf_size) return;
    }
    if (with_zone) snprintf(buf + used, buf_size - used, "Z");
}

int64_t rt_timestamp_to_iso(int64_t micros) {
    CoreHostCivilTime ct;
    char buf[64];
    core_host_micros_to_civil(micros, &ct);
    core_host_format_civil(&ct, 'T', 1, buf, sizeof(buf));
    return core_host_text_result(buf);
}

int64_t rt_timestamp_to_string(int64_t micros) {
    CoreHostCivilTime ct;
    char buf[64];
    core_host_micros_to_civil(micros, &ct);
    core_host_format_civil(&ct, ' ', 0, buf, sizeof(buf));
    return core_host_text_result(buf);
}

int64_t rt_time_now_iso(void) {
    int64_t micros = rt_time_now_unix_micros();
    if (micros < 0) return rt_string_new(NULL, 0);
    /* Whole-second resolution: the current-time ISO text is a display value. */
    return rt_timestamp_to_iso(core_host_floor_div(micros, 1000000LL) * 1000000LL);
}

/* ---- text -> timestamp (micros; -1 on malformed input) ---- */

static int core_host_scan_digits(const char** cursor, int min_digits,
                                 int max_digits, int64_t* out) {
    const char* p = *cursor;
    int64_t value = 0;
    int count = 0;
    while (count < max_digits && *p >= '0' && *p <= '9') {
        value = value * 10 + (*p - '0');
        p++;
        count++;
    }
    if (count < min_digits) return 0;
    *cursor = p;
    *out = value;
    return 1;
}

/* Accepts: YYYY-MM-DD, optionally followed by ('T'|'t'|' ') HH:MM:SS,
 * optionally .fraction (truncated to micros), optionally 'Z'|'z' or a
 * +HH:MM / -HH[:]MM offset (applied). Leading '-' year sign is accepted. */
static int64_t core_host_parse_timestamp(const char* s) {
    const char* p = s;
    int64_t year, month, day;
    int64_t hour = 0, minute = 0, second = 0, fraction = 0;
    int negative_year = 0;
    if (*p == '-') { negative_year = 1; p++; }
    if (!core_host_scan_digits(&p, 4, 6, &year)) return -1;
    if (negative_year) year = -year;
    if (*p != '-') return -1;
    p++;
    if (!core_host_scan_digits(&p, 2, 2, &month)) return -1;
    if (*p != '-') return -1;
    p++;
    if (!core_host_scan_digits(&p, 2, 2, &day)) return -1;
    if (month < 1 || month > 12 || day < 1) return -1;
    {
        static const int64_t month_days[12] = {31, 28, 31, 30, 31, 30,
                                               31, 31, 30, 31, 30, 31};
        int64_t day_limit = month_days[month - 1];
        if (month == 2 &&
            (year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)))
            day_limit = 29;
        if (day > day_limit) return -1;
    }
    if (*p == 'T' || *p == 't' || *p == ' ') {
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &hour)) return -1;
        if (*p != ':') return -1;
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &minute)) return -1;
        if (*p != ':') return -1;
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &second)) return -1;
        if (hour > 23 || minute > 59 || second > 60) return -1;
        if (*p == '.') {
            p++;
            int64_t scale = 100000;
            int digits = 0;
            while (*p >= '0' && *p <= '9') {
                if (digits < 6) {
                    fraction += (int64_t)(*p - '0') * scale;
                    scale /= 10;
                }
                digits++;
                p++;
            }
            if (digits == 0) return -1;
        }
    }
    int64_t offset_seconds = 0;
    if (*p == 'Z' || *p == 'z') {
        p++;
    } else if (*p == '+' || *p == '-') {
        int64_t sign = *p == '+' ? 1 : -1;
        int64_t off_hour, off_minute = 0;
        p++;
        if (!core_host_scan_digits(&p, 2, 2, &off_hour)) return -1;
        if (*p == ':') {
            p++;
            if (!core_host_scan_digits(&p, 2, 2, &off_minute)) return -1;
        } else if (*p >= '0' && *p <= '9' &&
                   !core_host_scan_digits(&p, 2, 2, &off_minute)) {
            return -1;
        }
        if (off_hour > 23 || off_minute > 59) return -1;
        offset_seconds = sign * (off_hour * 3600 + off_minute * 60);
    }
    if (*p != '\0') return -1;
    int64_t days = core_host_ymd_to_days(year, month, day);
    int64_t secs = days * 86400LL + hour * 3600 + minute * 60 + second
                 - offset_seconds;
    return secs * 1000000LL + fraction;
}

int64_t rt_timestamp_from_iso(int64_t iso_value) {
    char buf[128];
    if (!core_text_arg(iso_value, buf, sizeof(buf))) return -1;
    return core_host_parse_timestamp(buf);
}

int64_t rt_timestamp_parse(int64_t text_value) {
    return rt_timestamp_from_iso(text_value);
}

/* Floor difference in whole seconds between two micros timestamps. */
int64_t rt_timestamp_diff_seconds(int64_t a, int64_t b) {
    return core_host_floor_div(a - b, 1000000LL);
}

/* ---- rt_time_format: strftime-subset formatter over UTC ----
 * ts is whole seconds since the epoch. Deliberately NOT CRT strftime: the
 * Windows UCRT parameter-validates unknown specifiers and aborts the
 * process, which would turn a bad format string into a crash. Supported:
 * %Y %m %d %H %M %S %F (=%Y-%m-%d) %T (=%H:%M:%S) %%. Any other specifier
 * fails closed to the empty string. */
int64_t rt_time_format(int64_t ts_seconds, int64_t fmt_value) {
    char fmt[256];
    if (!core_text_arg(fmt_value, fmt, sizeof(fmt))) return rt_string_new(NULL, 0);
    if (ts_seconds > INT64_MAX / 1000000LL || ts_seconds < INT64_MIN / 1000000LL)
        return rt_string_new(NULL, 0);
    CoreHostCivilTime ct;
    core_host_micros_to_civil(ts_seconds * 1000000LL, &ct);
    char out[512];
    size_t used = 0;
    const char* p = fmt;
    for (; *p != '\0'; p++) {
        char piece[40];
        if (*p == '%') {
            p++;
            switch (*p) {
                case 'Y': snprintf(piece, sizeof(piece), "%04lld", (long long)ct.year); break;
                case 'm': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.month); break;
                case 'd': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.day); break;
                case 'H': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.hour); break;
                case 'M': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.minute); break;
                case 'S': snprintf(piece, sizeof(piece), "%02lld", (long long)ct.second); break;
                case 'F': snprintf(piece, sizeof(piece), "%04lld-%02lld-%02lld",
                                   (long long)ct.year, (long long)ct.month, (long long)ct.day); break;
                case 'T': snprintf(piece, sizeof(piece), "%02lld:%02lld:%02lld",
                                   (long long)ct.hour, (long long)ct.minute, (long long)ct.second); break;
                case '%': piece[0] = '%'; piece[1] = '\0'; break;
                default: return rt_string_new(NULL, 0);
            }
        } else {
            piece[0] = *p;
            piece[1] = '\0';
        }
        size_t piece_len = strlen(piece);
        if (used + piece_len >= sizeof(out)) return rt_string_new(NULL, 0);
        memcpy(out + used, piece, piece_len);
        used += piece_len;
    }
    return rt_string_new((const uint8_t*)out, (uint64_t)used);
}

/* ---- System singles ---- */

int64_t rt_cpu_count(void) {
#if defined(_WIN32)
    return spl_windows_active_processor_count();
#elif defined(__FreeBSD__)
    /* FreeBSD hides the non-POSIX _SC_NPROCESSORS_ONLN the same way macOS
     * does (see the _DARWIN_C_SOURCE note at the top of this file); the
     * native sysctl is the documented FreeBSD path. */
    int cpus = 0;
    size_t cpus_len = sizeof(cpus);
    if (sysctlbyname("kern.smp.cpus", &cpus, &cpus_len, NULL, 0) == 0 &&
        cpus > 0) {
        return (int64_t)cpus;
    }
    return -1;
#else
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? (int64_t)count : -1;
#endif
}


/* ---- CPU topology + thread pinning (build-runner fiber scheduler) ----------
 * Platform-neutral surface behind std.nogc_sync_mut.platform.host_io:
 *   rt_cpu_topology_count()          logical processors across ALL groups
 *   rt_cpu_topology_field(i, f)      f: 0 group, 1 number in group (Linux/
 *                                    FreeBSD: OS cpu id), 2 socket/package,
 *                                    3 NUMA node; -1 when out of range
 *   rt_thread_pin_current(i)         pin the calling thread to entry i
 *   rt_thread_current_cpu()          (group << 16) | number of the CPU now
 *                                    running the caller, -1 if unknown
 * Windows enumerates every processor group (a host with > 64 logical CPUs
 * has several; a thread stays in its process's initial group unless it is
 * assigned explicitly with SetThreadGroupAffinity). macOS has no affinity
 * API: pinning reports false there. Rust twin: runtime/src/cpu_topology.rs. */
#define RT_TOPO_MAX 1024
typedef struct { int32_t group, number, socket, numa; } RtTopoCpu;
static RtTopoCpu spl_topo_cpus[RT_TOPO_MAX];
static int32_t spl_topo_n = -1;

#if defined(_WIN32)
static INIT_ONCE spl_topo_once = INIT_ONCE_STATIC_INIT;
static int spl_topo_find(LOGICAL_PROCESSOR_RELATIONSHIP rel, WORD group, BYTE number) {
    DWORD len = 0;
    GetLogicalProcessorInformationEx(rel, NULL, &len);
    if (len == 0) return 0;
    BYTE* buf = (BYTE*)malloc(len);
    if (!buf) return 0;
    int result = 0, index = 0;
    if (GetLogicalProcessorInformationEx(rel, (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)buf, &len)) {
        for (DWORD off = 0; off < len;) {
            PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX e = (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)(buf + off);
            if (rel == RelationProcessorPackage) {
                for (WORD g = 0; g < e->Processor.GroupCount; g++) {
                    GROUP_AFFINITY* a = &e->Processor.GroupMask[g];
                    if (a->Group == group && (a->Mask >> number) & 1) result = index;
                }
                index++;
            } else if (rel == RelationNumaNode) {
#if defined(__MINGW32__)
                /* MinGW-w64 exposes the original one-group NUMA layout. */
                GROUP_AFFINITY* a = &e->NumaNode.GroupMask;
                if (a->Group == group && (a->Mask >> number) & 1)
                    result = (int)e->NumaNode.NodeNumber;
#else
                WORD count = e->NumaNode.GroupCount ? e->NumaNode.GroupCount : 1;
                for (WORD g = 0; g < count; g++) {
                    GROUP_AFFINITY* a = &e->NumaNode.GroupMasks[g];
                    if (a->Group == group && (a->Mask >> number) & 1) result = (int)e->NumaNode.NodeNumber;
                }
#endif
            }
            off += e->Size;
        }
    }
    free(buf);
    return result;
}
static BOOL CALLBACK spl_topo_init(PINIT_ONCE once, PVOID param, PVOID* ctx) {
    (void)once; (void)param; (void)ctx;
    int32_t n = 0;
    WORD groups = GetActiveProcessorGroupCount();
    for (WORD g = 0; g < groups && n < RT_TOPO_MAX; g++) {
        DWORD count = GetActiveProcessorCount(g);
        for (DWORD p = 0; p < count && n < RT_TOPO_MAX; p++) {
            spl_topo_cpus[n].group = g;
            spl_topo_cpus[n].number = (int32_t)p;
            spl_topo_cpus[n].socket = spl_topo_find(RelationProcessorPackage, g, (BYTE)p);
            spl_topo_cpus[n].numa = spl_topo_find(RelationNumaNode, g, (BYTE)p);
            n++;
        }
    }
    spl_topo_n = n;
    return TRUE;
}
static void spl_topo_ensure(void) { InitOnceExecuteOnce(&spl_topo_once, spl_topo_init, NULL, NULL); }
#else
#include <pthread.h>
#if defined(__linux__)
#include <sched.h>
#endif
#include <dirent.h>
#include <stdio.h>
static pthread_once_t spl_topo_once = PTHREAD_ONCE_INIT;
static int spl_topo_read_int(const char* path, int fallback) {
    FILE* f = fopen(path, "r");
    if (!f) return fallback;
    int v = fallback;
    if (fscanf(f, "%d", &v) != 1) v = fallback;
    fclose(f);
    return v;
}
static void spl_topo_init(void) {
    int32_t n = 0;
    long conf = sysconf(_SC_NPROCESSORS_CONF);
    char path[160];
    for (long cpu = 0; cpu < conf && n < RT_TOPO_MAX; cpu++) {
        snprintf(path, sizeof(path), "/sys/devices/system/cpu/cpu%ld/online", cpu);
        if (cpu > 0 && spl_topo_read_int(path, 1) == 0) continue;
        snprintf(path, sizeof(path), "/sys/devices/system/cpu/cpu%ld/topology/physical_package_id", cpu);
        int socket = spl_topo_read_int(path, 0);
        int numa = 0;
        snprintf(path, sizeof(path), "/sys/devices/system/cpu/cpu%ld", cpu);
        DIR* d = opendir(path);
        if (d) {
            struct dirent* ent;
            while ((ent = readdir(d)) != NULL) {
                if (strncmp(ent->d_name, "node", 4) == 0 && ent->d_name[4] >= '0' && ent->d_name[4] <= '9') {
                    numa = atoi(ent->d_name + 4);
                    break;
                }
            }
            closedir(d);
        }
        spl_topo_cpus[n].group = 0;
        spl_topo_cpus[n].number = (int32_t)cpu;
        spl_topo_cpus[n].socket = socket < 0 ? 0 : socket;
        spl_topo_cpus[n].numa = numa;
        n++;
    }
    spl_topo_n = n;
}
static void spl_topo_ensure(void) { pthread_once(&spl_topo_once, spl_topo_init); }
#endif

int64_t rt_cpu_topology_count(void) {
    spl_topo_ensure();
    return spl_topo_n;
}

int64_t rt_cpu_topology_field(int64_t index, int64_t field) {
    spl_topo_ensure();
    if (index < 0 || index >= spl_topo_n) return -1;
    const RtTopoCpu* c = &spl_topo_cpus[index];
    switch (field) {
        case 0: return c->group;
        case 1: return c->number;
        case 2: return c->socket;
        case 3: return c->numa;
        default: return -1;
    }
}

bool rt_thread_pin_current(int64_t index) {
    spl_topo_ensure();
    if (index < 0 || index >= spl_topo_n) return false;
    const RtTopoCpu* c = &spl_topo_cpus[index];
#if defined(_WIN32)
    GROUP_AFFINITY affinity;
    memset(&affinity, 0, sizeof(affinity));
    affinity.Group = (WORD)c->group;
    affinity.Mask = (KAFFINITY)1 << c->number;
    return SetThreadGroupAffinity(GetCurrentThread(), &affinity, NULL) != 0;
#elif defined(__linux__)
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(c->number, &set);
    return pthread_setaffinity_np(pthread_self(), sizeof(set), &set) == 0;
#else
    (void)c;
    return false;
#endif
}

int64_t rt_thread_current_cpu(void) {
#if defined(_WIN32)
    PROCESSOR_NUMBER pn;
    GetCurrentProcessorNumberEx(&pn);
    return ((int64_t)pn.Group << 16) | (int64_t)pn.Number;
#elif defined(__linux__)
    int cpu = sched_getcpu();
    return cpu < 0 ? -1 : (int64_t)cpu;
#else
    return -1;
#endif
}
/* OS CSPRNG fill -- same provider shape as rt_random_hex in runtime_native.c
 * (BCryptGenRandom via bcrypt.dll on Windows, /dev/urandom elsewhere).
 * Returns 0 on failure; never degrades to a weak source. */
static int core_host_entropy(unsigned char* out, size_t len) {
#if defined(_WIN32)
    typedef long (WINAPI *BCryptGenRandomFn)(void*, unsigned char*, unsigned long, unsigned long);
    if (len > 0xffffffffu) return 0;
    HMODULE library = LoadLibraryA("bcrypt.dll");
    if (!library) return 0;
    BCryptGenRandomFn fill = (BCryptGenRandomFn)GetProcAddress(library, "BCryptGenRandom");
    long status = fill ? fill(NULL, out, (unsigned long)len, 0x00000002) : -1;
    FreeLibrary(library);
    return status == 0;
#else
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd < 0) return 0;
    size_t offset = 0;
    while (offset < len) {
        ssize_t count = read(fd, out + offset, len - offset);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) { close(fd); return 0; }
        offset += (size_t)count;
    }
    close(fd);
    return 1;
#endif
}

/* RFC 4122 version-4 UUID from the OS CSPRNG, lowercase 8-4-4-4-12.
 * Empty text on entropy failure (the facade treats empty as failure). */
int64_t rt_uuid_v4(void) {
    unsigned char bytes[16];
    if (!core_host_entropy(bytes, sizeof(bytes))) return rt_string_new(NULL, 0);
    bytes[6] = (unsigned char)(0x40 | (bytes[6] & 0x0f));
    bytes[8] = (unsigned char)(0x80 | (bytes[8] & 0x3f));
    char buf[37];
    snprintf(buf, sizeof(buf),
        "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5],
        bytes[6], bytes[7], bytes[8], bytes[9], bytes[10], bytes[11],
        bytes[12], bytes[13], bytes[14], bytes[15]);
    return rt_string_new((const uint8_t*)buf, 36u);
}
