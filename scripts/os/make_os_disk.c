/*
 * Native SimpleOS FAT32 image builder.
 *
 * This keeps scripts/os/make_os_disk.shs independent of Python while
 * preserving the real FAT32 image and optional x86_64 ESP sidecar behavior.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#ifdef _WIN32
#include <direct.h>
#endif

enum {
    SECTOR_SIZE = 512,
    DEFAULT_TOTAL_SECTORS = 131072, /* 64 MiB */
    RESERVED_SECTORS = 32,
    FAT_COUNT = 1,
    ROOT_CLUSTER = 2,
    DIRECTORY_BYTES = 4096,
    DIRECTORY_ENTRY_CAPACITY = DIRECTORY_BYTES / 32,
    FAT32_MIN_DATA_CLUSTERS = 65525,
    SIMPLEOS_REPLACE_DESCRIPTOR_SECTOR = 2,
    SIMPLEOS_REPLACE_JOURNAL_START = 16,
    SIMPLEOS_REPLACE_JOURNAL_SECTORS = 16,
};

struct bytes {
    unsigned char *data;
    size_t len;
};

static void wipe_bytes(struct bytes bytes)
{
    volatile unsigned char *p = bytes.data;
    for (size_t i = 0; p && i < bytes.len; ++i)
        p[i] = 0;
}

static unsigned char *g_image;
static uint32_t *g_fat;
static size_t g_image_size;
static int g_next_cluster = 3;

/* Geometry derived from the SIZE_MB argument (argv[3] of the binary /
 * SIZE_BITS positional of make_os_disk.shs). Defaults preserve the historical
 * 64 MiB layout when the argument is missing/unparseable. */
static uint32_t g_total_sectors = DEFAULT_TOTAL_SECTORS;
static uint32_t g_fat_size_sectors;
static uint32_t g_data_start_sector;
static uint32_t g_data_cluster_count;
static uint32_t g_sectors_per_cluster;
static size_t g_cluster_size;
static size_t g_fat_entry_count;

static void die(const char *msg);

static void geometry_for_cluster_size(uint32_t sectors_per_cluster,
                                      uint32_t *fat_size_sectors,
                                      uint32_t *data_cluster_count)
{
    uint32_t fat_sectors = 1;
    uint32_t clusters = 0;
    for (int iteration = 0; iteration < 32; ++iteration) {
        uint32_t metadata_sectors = RESERVED_SECTORS + FAT_COUNT * fat_sectors;
        if (metadata_sectors >= g_total_sectors)
            break;
        clusters = (g_total_sectors - metadata_sectors) / sectors_per_cluster;
        uint32_t next_fat_sectors =
            ((clusters + 2u) * 4u + SECTOR_SIZE - 1u) / SECTOR_SIZE;
        if (next_fat_sectors == fat_sectors)
            break;
        fat_sectors = next_fat_sectors;
    }
    uint32_t metadata_sectors = RESERVED_SECTORS + FAT_COUNT * fat_sectors;
    clusters = metadata_sectors < g_total_sectors
        ? (g_total_sectors - metadata_sectors) / sectors_per_cluster
        : 0;
    *fat_size_sectors = fat_sectors;
    *data_cluster_count = clusters;
}

static void init_geometry(const char *size_mb_arg)
{
    long mb = size_mb_arg ? strtol(size_mb_arg, NULL, 10) : 0;
    if (mb >= 16 && mb <= 8192)
        g_total_sectors = (uint32_t)mb * 2048u; /* MB -> 512-byte sectors */

    static const uint32_t candidates[] = {64, 32, 16, 8, 4, 2, 1};
    g_sectors_per_cluster = 0;
    for (size_t i = 0; i < sizeof(candidates) / sizeof(candidates[0]); ++i) {
        uint32_t fat_sectors = 0;
        uint32_t clusters = 0;
        geometry_for_cluster_size(candidates[i], &fat_sectors, &clusters);
        if (clusters >= FAT32_MIN_DATA_CLUSTERS) {
            g_sectors_per_cluster = candidates[i];
            g_fat_size_sectors = fat_sectors;
            g_data_cluster_count = clusters;
            break;
        }
    }
    if (g_sectors_per_cluster == 0)
        die("disk image is too small for a valid FAT32 data-cluster count");

    g_data_start_sector = RESERVED_SECTORS + FAT_COUNT * g_fat_size_sectors;
    g_cluster_size = (size_t)SECTOR_SIZE * g_sectors_per_cluster;
    g_fat_entry_count = (size_t)g_fat_size_sectors * SECTOR_SIZE / 4;
}

static void die(const char *msg)
{
    fprintf(stderr, "%s\n", msg);
    exit(1);
}

static void *xcalloc(size_t count, size_t size)
{
    void *ptr = calloc(count, size);
    if (!ptr)
        die("allocation failed");
    return ptr;
}

static void le16(size_t offset, uint16_t value)
{
    g_image[offset] = (unsigned char)(value & 0xff);
    g_image[offset + 1] = (unsigned char)((value >> 8) & 0xff);
}

static void le32(size_t offset, uint32_t value)
{
    g_image[offset] = (unsigned char)(value & 0xff);
    g_image[offset + 1] = (unsigned char)((value >> 8) & 0xff);
    g_image[offset + 2] = (unsigned char)((value >> 16) & 0xff);
    g_image[offset + 3] = (unsigned char)((value >> 24) & 0xff);
}

static void write_u16(unsigned char *data, size_t offset, uint16_t value)
{
    data[offset] = (unsigned char)(value & 0xff);
    data[offset + 1] = (unsigned char)((value >> 8) & 0xff);
}

static void write_u32(unsigned char *data, size_t offset, uint32_t value)
{
    data[offset] = (unsigned char)(value & 0xff);
    data[offset + 1] = (unsigned char)((value >> 8) & 0xff);
    data[offset + 2] = (unsigned char)((value >> 16) & 0xff);
    data[offset + 3] = (unsigned char)((value >> 24) & 0xff);
}

static void write_u64(unsigned char *data, size_t offset, uint64_t value)
{
    for (int i = 0; i < 8; ++i)
        data[offset + (size_t)i] = (unsigned char)((value >> (i * 8)) & 0xff);
}

static uint32_t crc32c_bytes(const unsigned char *data, size_t len)
{
    uint32_t crc = 0xffffffffU;
    for (size_t i = 0; i < len; ++i) {
        crc ^= data[i];
        for (int bit = 0; bit < 8; ++bit)
            crc = (crc >> 1) ^ (0x82f63b78U & (uint32_t)-(int32_t)(crc & 1U));
    }
    return ~crc;
}

/* SimpleOS FAT32 extension descriptor.  It lives in reserved sector 2 and
 * points at the fixed journal in reserved sectors 16..31.  Neither region is
 * addressable as a FAT cluster, so runtime allocation can never claim it. */
static void write_atomic_replace_descriptor(void)
{
    unsigned char *descriptor = g_image +
        (size_t)SIMPLEOS_REPLACE_DESCRIPTOR_SECTOR * SECTOR_SIZE;
    memset(descriptor, 0, SECTOR_SIZE);
    write_u32(descriptor, 0, 0x44524153U); /* "SARD", little endian */
    write_u32(descriptor, 4, 1U);
    write_u32(descriptor, 8, SIMPLEOS_REPLACE_JOURNAL_START);
    write_u32(descriptor, 12, SIMPLEOS_REPLACE_JOURNAL_SECTORS);
    write_u32(descriptor, 16, SECTOR_SIZE);
    write_u32(descriptor, 20, 0U);
    write_u32(descriptor, 20, crc32c_bytes(descriptor, SECTOR_SIZE));
}

static size_t cluster_offset(int cluster)
{
    return ((size_t)g_data_start_sector +
            (size_t)(cluster - 2) * g_sectors_per_cluster) * SECTOR_SIZE;
}

static int reserve_clusters(size_t len)
{
    int needed = (int)((len + g_cluster_size - 1) / g_cluster_size);
    if (needed < 1)
        needed = 1;
    if ((uint64_t)g_next_cluster + (uint64_t)needed >
            (uint64_t)g_data_cluster_count + 2u ||
        (size_t)g_next_cluster + (size_t)needed > g_fat_entry_count)
        die("disk image too small for payload set");
    int first = g_next_cluster;
    for (int i = 0; i < needed; ++i) {
        int cluster = first + i;
        g_fat[cluster] = (i + 1 < needed) ? (uint32_t)(cluster + 1) : 0x0fffffffU;
    }
    g_next_cluster += needed;
    return first;
}

static int alloc_clusters(const unsigned char *data, size_t len)
{
    int first = reserve_clusters(len);
    int needed = (int)((len + g_cluster_size - 1) / g_cluster_size);
    if (needed < 1)
        needed = 1;
    for (int i = 0; i < needed; ++i) {
        int cluster = first + i;
        size_t start = (size_t)i * g_cluster_size;
        size_t chunk = len > start ? len - start : 0;
        if (chunk > g_cluster_size)
            chunk = g_cluster_size;
        if (cluster_offset(cluster) + chunk > g_image_size)
            die("disk image too small for payload set");
        if (chunk > 0)
            memcpy(g_image + cluster_offset(cluster), data + start, chunk);
    }
    return first;
}

static int alloc_directory(void)
{
    return reserve_clusters(DIRECTORY_BYTES);
}

static void reserve_root_directory(void)
{
    if (g_cluster_size >= DIRECTORY_BYTES)
        return;
    int continuation = reserve_clusters(DIRECTORY_BYTES - g_cluster_size);
    g_fat[ROOT_CLUSTER] = (uint32_t)continuation;
}

static struct bytes text_bytes(const char *text)
{
    struct bytes out;
    out.len = strlen(text);
    out.data = (unsigned char *)xcalloc(out.len + 1, 1);
    memcpy(out.data, text, out.len);
    return out;
}

static struct bytes textf(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    int needed = vsnprintf(NULL, 0, fmt, args);
    va_end(args);
    if (needed < 0)
        die("format failed");
    struct bytes out;
    out.len = (size_t)needed;
    out.data = (unsigned char *)xcalloc(out.len + 1, 1);
    va_start(args, fmt);
    vsnprintf((char *)out.data, out.len + 1, fmt, args);
    va_end(args);
    return out;
}

static struct bytes read_file(const char *path)
{
    struct bytes out = {0};
    if (!path || path[0] == '\0')
        return out;
    FILE *file = fopen(path, "rb");
    if (!file)
        return out;
    fseek(file, 0, SEEK_END);
    long size = ftell(file);
    if (size < 0) {
        fclose(file);
        return out;
    }
    fseek(file, 0, SEEK_SET);
    out.len = (size_t)size;
    out.data = (unsigned char *)xcalloc(out.len + 1, 1);
    if (out.len > 0 && fread(out.data, 1, out.len, file) != out.len)
        die("file read failed");
    fclose(file);
    return out;
}

static struct bytes read_sibling_file(const char *path, const char *leaf)
{
    char sibling[1024];
    const char *slash = path ? strrchr(path, '/') : NULL;
    size_t prefix_len = slash ? (size_t)(slash - path + 1) : 0;
    size_t leaf_len = strlen(leaf);
    if (!path || prefix_len + leaf_len >= sizeof(sibling))
        die("font companion path too long");
    if (prefix_len)
        memcpy(sibling, path, prefix_len);
    memcpy(sibling + prefix_len, leaf, leaf_len + 1);
    return read_file(sibling);
}

static struct bytes read_cfat4k_baseline(void)
{
    const char *override = getenv("SIMPLEOS_CFAT4K_BASELINE");
    if (override && override[0] != '\0')
        return read_file(override);
    return read_file("build/os/perf/CFAT4K.TXT");
}

static struct bytes read_simpleos_simple_payload(void)
{
    const char *override = getenv("SIMPLEOS_SIMPLE_BINARY");
    if (override && override[0] != '\0')
        return read_file(override);
    struct bytes stage3 = read_file("build/bootstrap/stage3/simple_simpleos");
    if (stage3.len)
        return stage3;
    struct bytes release_triple = read_file("bin/release/x86_64-unknown-simpleos/simple");
    if (release_triple.len)
        return release_triple;
    return read_file("bin/release/x86_64-simpleos/simple");
}

static bool is_elf_payload(struct bytes payload)
{
    return payload.len >= 4 &&
        payload.data[0] == 0x7f &&
        payload.data[1] == 'E' &&
        payload.data[2] == 'L' &&
        payload.data[3] == 'F';
}

static bool is_smf_payload(struct bytes payload)
{
    if (payload.len >= 128) {
        size_t off = payload.len - 128;
        if (payload.data[off] == 'S' && payload.data[off + 1] == 'M' && payload.data[off + 2] == 'F')
            return true;
    }
    return payload.len >= 3 &&
        payload.data[0] == 'S' &&
        payload.data[1] == 'M' &&
        payload.data[2] == 'F';
}

static void put_dir_entry(unsigned char *entries, int *count, const char *name, int cluster, size_t size, unsigned char attr)
{
    if (strlen(name) != 11)
        die("bad FAT short name");
    if (*count < 0 || *count >= DIRECTORY_ENTRY_CAPACITY)
        die("FAT directory entry capacity exceeded");
    unsigned char *entry = entries + ((size_t)(*count) * 32U);
    memset(entry, 0, 32);
    memcpy(entry, name, 11);
    entry[11] = attr;
    write_u16(entry, 20, (uint16_t)(((uint32_t)cluster >> 16) & 0xffffU));
    write_u16(entry, 26, (uint16_t)((uint32_t)cluster & 0xffffU));
    write_u32(entry, 28, (uint32_t)size);
    *count += 1;
}

static void font_companion_fat_name(char out[12], const char *font_name, const char *extension)
{
    size_t extension_len = strlen(extension);
    if (extension_len > 3)
        die("bad font companion extension");
    memcpy(out, font_name, 8);
    memset(out + 8, ' ', 3);
    memcpy(out + 8, extension, extension_len);
    out[11] = '\0';
}

static unsigned char fat_lfn_checksum(const char *short_name)
{
    unsigned char sum = 0;
    for (int i = 0; i < 11; ++i)
        sum = (unsigned char)(((sum & 1U) ? 0x80U : 0U) + (sum >> 1) + (unsigned char)short_name[i]);
    return sum;
}

static void put_named_dir_entry(unsigned char *entries, int *count, const char *short_name,
                                const char *long_name, int cluster, size_t size, unsigned char attr)
{
    size_t len = strlen(long_name);
    int parts = (int)((len + 12U) / 13U);
    if (parts <= 0 || *count < 0 ||
        *count + parts + 1 > DIRECTORY_ENTRY_CAPACITY)
        die("FAT long-name directory entry capacity exceeded");
    static const unsigned char offsets[13] = {1, 3, 5, 7, 9, 14, 16, 18, 20, 22, 24, 28, 30};
    unsigned char checksum = fat_lfn_checksum(short_name);
    for (int part = parts; part >= 1; --part) {
        unsigned char *entry = entries + ((size_t)(*count) * 32U);
        memset(entry, 0xff, 32);
        entry[0] = (unsigned char)(part | (part == parts ? 0x40 : 0));
        entry[11] = 0x0f;
        entry[12] = 0;
        entry[13] = checksum;
        entry[26] = 0;
        entry[27] = 0;
        size_t start = (size_t)(part - 1) * 13U;
        for (int i = 0; i < 13; ++i) {
            size_t index = start + (size_t)i;
            uint16_t ch = index < len ? (unsigned char)long_name[index] : (index == len ? 0 : 0xffffU);
            write_u16(entry, offsets[i], ch);
        }
        *count += 1;
    }
    put_dir_entry(entries, count, short_name, cluster, size, attr);
}

/* FAT32 mandates "." and ".." as the first two entries of every subdirectory;
 * without them fsck reports "Expected a valid '.' entry in the first slot, found
 * free entry" and the directory is not traversable. Call this on a subdirectory
 * buffer BEFORE any content lands in it. Per spec, ".." carries cluster 0 when
 * the parent is the root directory — callers pass 0, not ROOT_CLUSTER, there. */
static void put_dot_entries(unsigned char *entries, int *count,
                            int self_cluster, int parent_cluster)
{
    put_dir_entry(entries, count, ".          ", self_cluster, 0, 0x10);
    put_dir_entry(entries, count, "..         ", parent_cluster, 0, 0x10);
}

static void write_directory(int cluster, const unsigned char *entries, int count)
{
    size_t bytes = (size_t)count * 32U;
    if (count < 0 || bytes > DIRECTORY_BYTES)
        die("FAT directory buffer overflow");
    if (cluster == ROOT_CLUSTER && bytes > DIRECTORY_BYTES)
        die("FAT root directory chain overflow");
    if (cluster_offset(cluster) + bytes > g_image_size)
        die("FAT directory exceeds image bounds");
    if (bytes > 0)
        memcpy(g_image + cluster_offset(cluster), entries, bytes);
}

static struct bytes elf_image(const char *marker, int machine, bool is64)
{
    size_t marker_len = strlen(marker) + 1;
    size_t header = is64 ? 64 : 52;
    size_t phdr = is64 ? 56 : 32;
    struct bytes out;
    out.len = header + phdr + marker_len;
    out.data = (unsigned char *)xcalloc(out.len, 1);
    out.data[0] = 0x7f;
    out.data[1] = 'E';
    out.data[2] = 'L';
    out.data[3] = 'F';
    out.data[4] = is64 ? 2 : 1;
    out.data[5] = 1;
    out.data[6] = 1;
    write_u16(out.data, 16, 2);
    write_u16(out.data, 18, (uint16_t)machine);
    write_u32(out.data, 20, 1);
    if (is64) {
        write_u64(out.data, 24, 0x1000);
        write_u64(out.data, 32, 64);
        write_u16(out.data, 52, 64);
        write_u16(out.data, 54, 56);
        write_u16(out.data, 56, 1);
        write_u32(out.data, 64, 1);
        write_u32(out.data, 68, 5);
        write_u64(out.data, 80, 0x1000);
        write_u64(out.data, 88, 0x1000);
        write_u64(out.data, 96, out.len);
        write_u64(out.data, 104, out.len);
        write_u64(out.data, 112, 0x1000);
    } else {
        write_u32(out.data, 24, 0x1000);
        write_u32(out.data, 28, 52);
        write_u16(out.data, 40, 52);
        write_u16(out.data, 42, 32);
        write_u16(out.data, 44, 1);
        write_u32(out.data, 52, 1);
        write_u32(out.data, 60, 0x1000);
        write_u32(out.data, 64, 0x1000);
        write_u32(out.data, 68, (uint32_t)out.len);
        write_u32(out.data, 72, (uint32_t)out.len);
        write_u32(out.data, 76, 5);
        write_u32(out.data, 80, 0x1000);
    }
    memcpy(out.data + header + phdr, marker, marker_len);
    return out;
}

static struct bytes smf(struct bytes payload)
{
    struct bytes out;
    out.len = payload.len + 128;
    out.data = (unsigned char *)xcalloc(out.len, 1);
    memcpy(out.data, payload.data, payload.len);
    memcpy(out.data + payload.len, "SMF", 3);
    write_u32(out.data, payload.len + 52, (uint32_t)payload.len);
    return out;
}

static const char *lane_for_platform(const char *platform)
{
    if (strcmp(platform, "riscv64") == 0)
        return "riscv64-hosted";
    if (strcmp(platform, "riscv32") == 0)
        return "riscv32-virtio-fat32-smf";
    if (strcmp(platform, "arm64") == 0)
        return "arm64-virtio-fat32-smf";
    if (strcmp(platform, "arm32") == 0)
        return "arm32-virtio-fat32-smf";
    if (strcmp(platform, "x86_32") == 0)
        return "x86_32-initrd-fat32-smf";
    return "x86_64-uefi-hardware";
}

static int machine_for_platform(const char *platform, bool *is64)
{
    *is64 = true;
    if (strcmp(platform, "riscv32") == 0) {
        *is64 = false;
        return 243;
    }
    if (strcmp(platform, "arm32") == 0) {
        *is64 = false;
        return 40;
    }
    if (strcmp(platform, "arm64") == 0)
        return 183;
    if (strcmp(platform, "x86_64") == 0)
        return 62;
    if (strcmp(platform, "x86_32") == 0) {
        *is64 = false;
        return 3;
    }
    return 243;
}

static struct bytes platform_elf(const char *platform, const char *marker)
{
    bool is64 = true;
    int machine = machine_for_platform(platform, &is64);
    return elf_image(marker, machine, is64);
}

static struct bytes app_elf(const char *platform, const char *suffix)
{
    char marker[256];
    snprintf(marker, sizeof(marker), "SIMPLEOS_%s_%s_ELF", platform, suffix);
    for (char *p = marker; *p; ++p)
        if (*p >= 'a' && *p <= 'z')
            *p = (char)(*p - 'a' + 'A');
    return smf(platform_elf(platform, marker));
}

static struct bytes simple_role_payload(const char *platform, const char *fallback_suffix, struct bytes simple_payload)
{
    if (simple_payload.len) {
        const char *override = getenv("SIMPLEOS_SIMPLE_BINARY");
        if (!is_elf_payload(simple_payload) && !is_smf_payload(simple_payload)) {
            if (override && override[0] != '\0')
                die("SIMPLEOS_SIMPLE_BINARY must point to a SimpleOS ELF or SMF payload");
            return app_elf(platform, fallback_suffix);
        }
        if (is_smf_payload(simple_payload))
            return simple_payload;
        return smf(simple_payload);
    }
    return app_elf(platform, fallback_suffix);
}

static void mkdir_p(const char *path)
{
    char tmp[2048];
    snprintf(tmp, sizeof(tmp), "%s", path);
    for (char *p = tmp + 1; *p; ++p) {
        if (*p == '/') {
            *p = '\0';
#ifdef _WIN32
            _mkdir(tmp);
#else
            mkdir(tmp, 0777);
#endif
            *p = '/';
        }
    }
#ifdef _WIN32
    _mkdir(tmp);
#else
    mkdir(tmp, 0777);
#endif
}

static void write_file_path(const char *path, const unsigned char *data, size_t len)
{
    FILE *file = fopen(path, "wb");
    if (!file) {
        perror(path);
        exit(1);
    }
    if (len > 0 && fwrite(data, 1, len, file) != len)
        die("file write failed");
    fclose(file);
}

static void maybe_write_esp(const char *img_path, const struct bytes *bootloader, const struct bytes *kernel, const struct bytes *limine)
{
    if (bootloader->len == 0)
        return;
    char base[1024];
    snprintf(base, sizeof(base), "%s", img_path);
    char *slash = strrchr(base, '/');
    if (slash)
        *slash = '\0';
    else
        snprintf(base, sizeof(base), ".");
    char boot_dir[1200];
    snprintf(boot_dir, sizeof(boot_dir), "%s/esp/EFI/BOOT", base);
    mkdir_p(boot_dir);
    char path[1400];
    snprintf(path, sizeof(path), "%s/BOOTX64.EFI", boot_dir);
    write_file_path(path, bootloader->data, bootloader->len);
    snprintf(path, sizeof(path), "%s/esp/kernel.elf", base);
    write_file_path(path, kernel->data, kernel->len);
    snprintf(path, sizeof(path), "%s/esp/limine.conf", base);
    write_file_path(path, limine->data, limine->len);
    snprintf(path, sizeof(path), "%s/limine.conf", boot_dir);
    write_file_path(path, limine->data, limine->len);
}

/* FAT32 FSInfo sector. The BPB DECLARES fsinfo_sector=1 (le16(48, 1) below);
 * leaving that sector zeroed made `fsck.fat` fail the image with "FSINFO sector
 * has bad magic number(s)" and the SimpleOS-WM evidence harness reject it as
 * invalid-fat32-structure. Offsets are spec-fixed: lead 0x41615252 at +0,
 * struct 0x61417272 at +484, trail 00 00 55 AA at +508.
 * free_count/next_free carry REAL values rather than 0xFFFFFFFF ("unknown");
 * unknown is spec-legal but fsck flags it as "Free cluster summary
 * uninitialized". Data clusters are numbered from 2, so used = g_next_cluster-2.
 * See doc/08_tracking/bug/simpleos_wm_fat32_image_fsinfo_uninitialized_2026-07-25.md */
static void write_fat32_fsinfo(size_t sector_offset)
{
    unsigned char *fsinfo = g_image + sector_offset;
    uint32_t allocated_clusters = (uint32_t)(g_next_cluster - 2);
    uint32_t free_clusters = allocated_clusters <= g_data_cluster_count
        ? g_data_cluster_count - allocated_clusters
        : 0;
    uint32_t next_free = (uint32_t)g_next_cluster < g_data_cluster_count + 2u
        ? (uint32_t)g_next_cluster
        : 0xffffffffU;

    memset(fsinfo, 0, SECTOR_SIZE);
    write_u32(fsinfo, 0, 0x41615252U);
    write_u32(fsinfo, 484, 0x61417272U);
    write_u32(fsinfo, 488, free_clusters);
    write_u32(fsinfo, 492, next_free);
    write_u32(fsinfo, 508, 0xaa550000U);
}

static void finish_fat32_image(const char *img_path)
{
    g_image[0] = 0xeb;
    g_image[1] = 0x58;
    g_image[2] = 0x90;
    memcpy(g_image + 3, "SIMPLEOS", 8);
    le16(11, SECTOR_SIZE);
    g_image[13] = (unsigned char)g_sectors_per_cluster;
    le16(14, RESERVED_SECTORS);
    g_image[16] = FAT_COUNT;
    g_image[21] = 0xf8;
    le16(24, 63);
    le16(26, 255);
    le32(32, g_total_sectors);
    le32(36, g_fat_size_sectors);
    le32(44, ROOT_CLUSTER);
    le16(48, 1);
    le16(50, 6);
    g_image[64] = 0x80;                 /* BS_DrvNum: fixed disk */
    /* Extended boot signature + volume label. 0x29 at offset 66 marks
     * vol-id/label/fs-type as present; the label field (offset 71, 11 bytes,
     * space-padded) left as zeros makes fsck report "Label '' stored in boot
     * sector is not valid. Auto-removing label". The spelling here MUST match
     * the root-directory ATTR_VOLUME_ID (0x08) entry exactly, padding included. */
    g_image[66] = 0x29;
    le32(67, 0x12345678U);              /* volume id (arbitrary but stable) */
    memcpy(g_image + 71, "SIMPLEOS   ", 11);
    memcpy(g_image + 82, "FAT32   ", 8);
    g_image[510] = 0x55;
    g_image[511] = 0xaa;

    /* Sector 6: backup boot sector, declared above by le16(50, 6) and otherwise
     * never written — fsck reported every BPB byte as differing from its
     * all-zero backup. A verbatim copy of sector 0 is what the spec wants; it
     * must be taken AFTER sector 0 is fully populated.
     * Sector 1 is the primary FSInfo; sector 7 is its copy inside the backup
     * boot region (backup of sectors 0..2 at 6..8), so both are written. */
    memcpy(g_image + (size_t)6 * SECTOR_SIZE, g_image, SECTOR_SIZE);
    write_fat32_fsinfo((size_t)1 * SECTOR_SIZE);
    write_fat32_fsinfo((size_t)7 * SECTOR_SIZE);
    write_atomic_replace_descriptor();

    unsigned char *fat_bytes = g_image + ((size_t)RESERVED_SECTORS * SECTOR_SIZE);
    for (size_t i = 0; i < (size_t)g_fat_size_sectors * SECTOR_SIZE / 4; ++i)
        write_u32(fat_bytes, i * 4, g_fat[i]);
    write_file_path(img_path, g_image, g_image_size);
}

static void write_desktop_font_image(
    const char *img_path,
    const char **font_fat_names,
    const char **font_long_names,
    struct bytes *font_payloads,
    struct bytes *font_metadata_payloads,
    struct bytes *font_license_payloads,
    struct bytes font_copyright_payload,
    struct bytes font_corpus_payload,
    struct bytes cldr_license_payload,
    struct bytes simple_license_payload,
    struct bytes third_party_notices_payload,
    struct bytes theme_payload)
{
    enum { FONT_ASSET_COUNT = 16 };
    int sys_cluster = alloc_directory();
    int fonts_cluster = alloc_directory();
    int font_clusters[FONT_ASSET_COUNT];
    int font_metadata_clusters[FONT_ASSET_COUNT];
    int font_license_clusters[FONT_ASSET_COUNT];
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        font_clusters[i] = alloc_clusters(font_payloads[i].data, font_payloads[i].len);
        font_metadata_clusters[i] = alloc_clusters(font_metadata_payloads[i].data, font_metadata_payloads[i].len);
        font_license_clusters[i] = alloc_clusters(font_license_payloads[i].data, font_license_payloads[i].len);
    }
    int font_copyright_cluster = alloc_clusters(font_copyright_payload.data, font_copyright_payload.len);
    int font_corpus_cluster = alloc_clusters(font_corpus_payload.data, font_corpus_payload.len);
    int cldr_license_cluster = alloc_clusters(cldr_license_payload.data, cldr_license_payload.len);
    int simple_license_cluster = alloc_clusters(simple_license_payload.data, simple_license_payload.len);
    int notices_cluster = alloc_clusters(third_party_notices_payload.data, third_party_notices_payload.len);
    int theme_cluster = theme_payload.len ? alloc_clusters(theme_payload.data, theme_payload.len) : 0;

    unsigned char root[DIRECTORY_BYTES] = {0};
    unsigned char sys[DIRECTORY_BYTES] = {0};
    unsigned char fonts[DIRECTORY_BYTES] = {0};
    int root_n = 0, sys_n = 0, fonts_n = 0;
    /* Volume label must exist BOTH in the boot sector (offset 71) and as a
     * root-directory entry with ATTR_VOLUME_ID (0x08), cluster 0, size 0. With
     * only the boot-sector half fsck reports "Label in boot sector is
     * 'SIMPLEOS', but there is no volume label in root directory". */
    put_dir_entry(root, &root_n, "SIMPLEOS   ", 0, 0, 0x08);
    put_dir_entry(root, &root_n, "SYS        ", sys_cluster, 0, 0x10);
    if (theme_cluster)
        put_dir_entry(root, &root_n, "THEME   CSS", theme_cluster, theme_payload.len, 0x20);
    put_dot_entries(sys, &sys_n, sys_cluster, 0);
    put_dir_entry(sys, &sys_n, "FONTS      ", fonts_cluster, 0, 0x10);
    put_dot_entries(fonts, &fonts_n, fonts_cluster, sys_cluster);
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        put_named_dir_entry(fonts, &fonts_n, font_fat_names[i], font_long_names[i],
                            font_clusters[i], font_payloads[i].len, 0x20);
        char metadata_name[12], license_name[12];
        font_companion_fat_name(metadata_name, font_fat_names[i], "PB");
        font_companion_fat_name(license_name, font_fat_names[i], i == 12 ? "LIC" : "OFL");
        put_dir_entry(fonts, &fonts_n, metadata_name,
                      font_metadata_clusters[i], font_metadata_payloads[i].len, 0x20);
        put_dir_entry(fonts, &fonts_n, license_name,
                      font_license_clusters[i], font_license_payloads[i].len, 0x20);
    }
    char copyright_name[12];
    font_companion_fat_name(copyright_name, font_fat_names[12], "CPY");
    put_dir_entry(fonts, &fonts_n, copyright_name,
                  font_copyright_cluster, font_copyright_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "CORPUS  SDN", font_corpus_cluster, font_corpus_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "CLDR    LIC", cldr_license_cluster, cldr_license_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "SIMPLE  LIC", simple_license_cluster, simple_license_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "NOTICES MD ", notices_cluster, third_party_notices_payload.len, 0x20);
    /* 93 = 91 font-bundle entries + the 2 mandatory FAT32 dot entries ("." and
     * "..") this directory now emits. The guard is KEPT (it catches a missing or
     * extra font asset); only the expected total moved, by exactly 2. */
    if (fonts_n != 93)
        die("SimpleOS desktop font bundle directory manifest mismatch");

    write_directory(ROOT_CLUSTER, root, root_n);
    write_directory(sys_cluster, sys, sys_n);
    write_directory(fonts_cluster, fonts, fonts_n);
    finish_fat32_image(img_path);
}

int main(int argc, char **argv)
{
    enum { FONT_ASSET_COUNT = 16 };
    static const char *font_env_names[FONT_ASSET_COUNT] = {
        "SIMPLEOS_FONT_ASSET_NSANSSC", "SIMPLEOS_FONT_ASSET_NSANSDEV",
        "SIMPLEOS_FONT_ASSET_NSANSARB", "SIMPLEOS_FONT_ASSET_NSANSBEN",
        "SIMPLEOS_FONT_ASSET_NSERIFSC", "SIMPLEOS_FONT_ASSET_NSERFDEV",
        "SIMPLEOS_FONT_ASSET_NNASKHAR", "SIMPLEOS_FONT_ASSET_NSERFBEN",
        "SIMPLEOS_FONT_ASSET_NOTOSANS", "SIMPLEOS_FONT_ASSET_BUNGEE",
        "SIMPLEOS_FONT_ASSET_NUNITO", "SIMPLEOS_FONT_ASSET_CAVEAT",
        "SIMPLEOS_FONT_ASSET_ROBOSLAB", "SIMPLEOS_FONT_ASSET_UNIFRAKT",
        "SIMPLEOS_FONT_ASSET_PIXELIFY", "SIMPLEOS_FONT_ASSET_NOTOEMOJ"
    };
    static const char *font_fat_names[FONT_ASSET_COUNT] = {
        "NSANSSC    ", "NSANSDEV   ", "NSANSARB   ", "NSANSBEN   ",
        "NSERIFSC   ", "NSERFDEV   ", "NNASKHAR   ", "NSERFBEN   ",
        "NOTOSANS   ", "BUNGEE     ", "NUNITO     ", "CAVEAT     ",
        "ROBOSLAB   ", "UNIFRAKT   ", "PIXELIFY   ", "NOTOEMOJ   "
    };
    static const char *font_long_names[FONT_ASSET_COUNT] = {
        "NotoSansSC[wght].ttf", "NotoSansDevanagari[wdth,wght].ttf",
        "NotoSansArabic[wdth,wght].ttf", "NotoSansBengali[wdth,wght].ttf",
        "NotoSerifSC[wght].ttf", "NotoSerifDevanagari[wdth,wght].ttf",
        "NotoNaskhArabic[wght].ttf", "NotoSerifBengali[wdth,wght].ttf",
        "NotoSansMono[wdth,wght].ttf", "Bungee-Regular.ttf",
        "Nunito[wght].ttf", "Caveat[wght].ttf",
        "RobotoSlab[wght].ttf", "UnifrakturCook-Bold.ttf",
        "PixelifySans[wght].ttf", "NotoEmoji[wght].ttf"
    };
    /* Compatibility overrides may relocate validated TTF bytes only. Keep
     * metadata/licenses anchored to the canonical pinned repository tree. */
    static const char *font_companion_anchor_paths[FONT_ASSET_COUNT] = {
        "assets/fonts/google-fonts/ofl/notosanssc/NotoSansSC[wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansdevanagari/NotoSansDevanagari[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansarabic/NotoSansArabic[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansbengali/NotoSansBengali[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notoserifsc/NotoSerifSC[wght].ttf",
        "assets/fonts/google-fonts/ofl/notoserifdevanagari/NotoSerifDevanagari[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notonaskharabic/NotoNaskhArabic[wght].ttf",
        "assets/fonts/google-fonts/ofl/notoserifbengali/NotoSerifBengali[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf",
        "assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf",
        "assets/fonts/google-fonts/ofl/nunito/Nunito[wght].ttf",
        "assets/fonts/google-fonts/ofl/caveat/Caveat[wght].ttf",
        "assets/fonts/google-fonts/apache/robotoslab/RobotoSlab[wght].ttf",
        "assets/fonts/google-fonts/ofl/unifrakturcook/UnifrakturCook-Bold.ttf",
        "assets/fonts/google-fonts/ofl/pixelifysans/PixelifySans[wght].ttf",
        "assets/fonts/google-fonts/ofl/notoemoji/NotoEmoji[wght].ttf"
    };
    if (argc != 5 && argc != 6)
        die("usage: make_os_disk IMAGE PLATFORM SIZE_BITS KERNEL [PROFILE]");
    const char *img_path = argv[1];
    const char *platform = argv[2];
    const char *kernel_path = argv[4];
    const char *profile = argc == 6 ? argv[5] : "fs-exec";
    bool desktop_fonts = strcmp(profile, "desktop-fonts") == 0;
    if (!desktop_fonts && strcmp(profile, "fs-exec") != 0)
        die("unsupported SimpleOS disk profile");
    const char *lane = lane_for_platform(platform);

    init_geometry(argv[3]);
    size_t image_size = (size_t)g_total_sectors * SECTOR_SIZE;
    g_image_size = image_size;
    g_image = (unsigned char *)xcalloc(image_size, 1);
    g_fat = (uint32_t *)xcalloc(g_fat_entry_count, sizeof(uint32_t));
    g_fat[0] = 0x0ffffff8U;
    g_fat[1] = 0x0fffffffU;
    g_fat[ROOT_CLUSTER] = 0x0fffffffU;
    reserve_root_directory();

    const char *hello_marker = strcmp(platform, "riscv64") == 0 ? "SIMPLEOS_RISCV64_HELLO_ELF" :
        strcmp(platform, "riscv32") == 0 ? "SIMPLEOS_RISCV32_HELLO_ELF" :
        strcmp(platform, "arm64") == 0 ? "SIMPLEOS_ARM64_HELLO_ELF" :
        strcmp(platform, "arm32") == 0 ? "SIMPLEOS_ARM32_HELLO_ELF" :
        strcmp(platform, "x86_32") == 0 ? "SIMPLEOS_X86_32_HELLO_ELF" : "SIMPLEOS_X86_64_HELLO_ELF";
    const char *gui_marker = strcmp(platform, "riscv64") == 0 ? "SIMPLEOS_RISCV64_GUI_ELF" :
        strcmp(platform, "riscv32") == 0 ? "SIMPLEOS_RISCV32_GUI_ELF" :
        strcmp(platform, "arm64") == 0 ? "SIMPLEOS_ARM64_GUI_ELF" :
        strcmp(platform, "arm32") == 0 ? "SIMPLEOS_ARM32_GUI_ELF" :
        strcmp(platform, "x86_32") == 0 ? "SIMPLEOS_X86_32_GUI_ELF" : "SIMPLEOS_X86_64_GUI_ELF";

    struct bytes kernel_file = read_file(kernel_path);
    struct bytes bootloader_file = read_file(getenv("SIMPLEOS_UEFI_BOOTLOADER"));
    struct bytes simple_payload = desktop_fonts ? (struct bytes){0} : read_simpleos_simple_payload();
    struct bytes clang_payload = read_file(getenv("SIMPLEOS_CLANG_BINARY"));
    struct bytes llc_payload = read_file(getenv("SIMPLEOS_LLC_BINARY"));
    struct bytes lld_payload = read_file(getenv("SIMPLEOS_LLD_BINARY"));
    struct bytes crt0_payload = read_file(getenv("SIMPLEOS_CRT0_OBJECT"));
    struct bytes runtime_payload = read_file(getenv("SIMPLEOS_RUNTIME_ARCHIVE"));
    struct bytes libc_payload = read_file(getenv("SIMPLEOS_LIBC_ARCHIVE"));
    struct bytes linker_script_payload = read_file(getenv("SIMPLEOS_LINKER_SCRIPT"));
    struct bytes simple_entry_payload = read_file(getenv("SIMPLEOS_SIMPLE_ENTRY_OBJECT"));
    struct bytes hello_object_payload = read_file(getenv("SIMPLEOS_HELLO_OBJECT"));
    struct bytes hello_ir_payload = read_file(getenv("SIMPLEOS_HELLO_IR"));
    struct bytes fsexec_payload = read_file(getenv("SIMPLEOS_FSEXEC_BINARY"));
    struct bytes servers_payload = read_file(getenv("SIMPLEOS_SERVERS_BINARY"));
    const char *server_credential_path = getenv("SIMPLEOS_SERVER_DB_CREDENTIAL_FILE");
    struct bytes server_credential = read_file(server_credential_path);
    if (servers_payload.len && (!server_credential_path || !server_credential_path[0] ||
                                !server_credential.len || server_credential.len > 128)) {
        wipe_bytes(server_credential);
        fprintf(stderr, "SIMPLEOS_SERVER_DB_CREDENTIAL_FILE must name a non-empty file of at most 128 bytes when staging SERVERS.ELF\n");
        return 1;
    }
    /* The fullscreen WM showcase stages a REAL freestanding browser client at
     * ::/SYS/APPS/BROWSMF.SMF. When SIMPLEOS_BROWSER_DEMO_BINARY is supplied it
     * is authoritative: an explicitly requested client must never be silently
     * replaced by the synthesized marker stub, so an unreadable/empty path is a
     * hard error rather than a fallback. The stub remains only for callers that
     * supply no binary at all (e.g. desktop-fonts profiles). */
    const char *browser_demo_path = getenv("SIMPLEOS_BROWSER_DEMO_BINARY");
    struct bytes browser_payload = read_file(getenv("SIMPLEOS_BROWSER_DEMO_BINARY"));
    if (browser_demo_path && browser_demo_path[0] != '\0' && !browser_payload.len) {
        fprintf(stderr, "SIMPLEOS_BROWSER_DEMO_BINARY could not be read: %s\n",
                browser_demo_path);
        return 1;
    }
    struct bytes font_payloads[FONT_ASSET_COUNT];
    struct bytes font_metadata_payloads[FONT_ASSET_COUNT];
    struct bytes font_license_payloads[FONT_ASSET_COUNT];
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        const char *font_asset_path = getenv(font_env_names[i]);
        if (!font_asset_path || font_asset_path[0] == '\0') {
            fprintf(stderr, "%s is required\n", font_env_names[i]);
            return 1;
        }
        font_payloads[i] = read_file(font_asset_path);
        if (!font_payloads[i].len) {
            fprintf(stderr, "%s could not be read\n", font_env_names[i]);
            return 1;
        }
        font_metadata_payloads[i] = read_sibling_file(font_companion_anchor_paths[i], "METADATA.pb");
        font_license_payloads[i] = read_sibling_file(
            font_companion_anchor_paths[i], i == 12 ? "LICENSE.txt" : "OFL.txt");
        if (!font_metadata_payloads[i].len || !font_license_payloads[i].len) {
            fprintf(stderr, "%s companion metadata/license could not be read\n", font_env_names[i]);
            return 1;
        }
    }
    struct bytes font_copyright_payload = read_sibling_file(font_companion_anchor_paths[12], "COPYRIGHT.txt");
    struct bytes font_corpus_payload = read_file("assets/fonts/google-fonts/CORPUS.sdn");
    struct bytes cldr_license_payload = read_file("assets/fonts/cldr/release-48-2/LICENSE");
    struct bytes simple_license_payload = read_file("LICENSE");
    struct bytes third_party_notices_payload = read_file("THIRD_PARTY_NOTICES.md");
    const char *theme_path = getenv("SIMPLEOS_WM_THEME_FILE");
    struct bytes theme_payload = read_file(theme_path);
    if (theme_path && theme_path[0] != '\0' && !theme_payload.len) {
        fprintf(stderr, "SIMPLEOS_WM_THEME_FILE could not be read: %s\n", theme_path);
        return 1;
    }
    if (!font_copyright_payload.len || !font_corpus_payload.len || !cldr_license_payload.len ||
        !simple_license_payload.len || !third_party_notices_payload.len)
        die("SimpleOS font bundle global notice could not be read");
    if (desktop_fonts) {
        write_desktop_font_image(
            img_path, font_fat_names, font_long_names, font_payloads,
            font_metadata_payloads, font_license_payloads, font_copyright_payload,
            font_corpus_payload, cldr_license_payload, simple_license_payload,
            third_party_notices_payload, theme_payload);
        return 0;
    }
    int efi_cluster = alloc_directory();
    int boot_cluster = alloc_directory();
    int sys_cluster = alloc_directory();
    int fonts_cluster = alloc_directory();
    int apps_cluster = alloc_directory();
    int perf_cluster = alloc_directory();
    int usr_cluster = alloc_directory();
    int usr_bin_cluster = alloc_directory();
    int usr_lib_cluster = alloc_directory();
    int bin_cluster = alloc_directory();
    int sysrt_cluster = alloc_directory();
    int tmp_cluster = alloc_directory();
    struct bytes cfat4k = read_cfat4k_baseline();
    struct bytes kernel = kernel_file.len ? kernel_file : text_bytes("SIMPLEOS_UEFI_KERNEL_MISSING\n");
    struct bytes bootloader = bootloader_file.len ? bootloader_file : text_bytes("SIMPLEOS_UEFI_BOOTLOADER_MISSING\n");
    struct bytes limine = text_bytes("timeout: 0\nserial: yes\n/ SimpleOS\nprotocol: multiboot1\npath: boot():/kernel.elf\ntextmode: no\nresolution: 1024x768x32\ncmdline: console=serial root=/dev/nvme0n1\n");
    struct bytes hello_txt = text_bytes("Hello from SimpleOS\n");
    struct bytes server_document = text_bytes("<html><body>SimpleOS filesystem server document</body></html>\n");
    static unsigned char qemu_nonce_slot_data[118];
    static const char qemu_nonce_placeholder[] =
        "SIMPLEOS_QEMU_NONCE=__SIMPLEOS_QEMU_NONCE_SLOT_V1__\n";
    memcpy(qemu_nonce_slot_data, qemu_nonce_placeholder,
           sizeof(qemu_nonce_placeholder) - 1U);
    struct bytes qemu_nonce_slot = {qemu_nonce_slot_data, sizeof(qemu_nonce_slot_data)};
    static unsigned char collector_nonce_slot_data[118];
    static const char collector_nonce_placeholder[] =
        "SOSIX_COLLECTOR_RUN_NONCE=__SOSIX_COLLECTOR_RUN_NONCE_SLOT_V1__\n";
    memcpy(collector_nonce_slot_data, collector_nonce_placeholder,
           sizeof(collector_nonce_placeholder) - 1U);
    struct bytes collector_nonce_slot = {
        collector_nonce_slot_data, sizeof(collector_nonce_slot_data)};
    struct bytes numbers_txt = text_bytes("5\n");
    struct bytes hello_spl = text_bytes("fn main() -> i64:\n    print \"Hello from SimpleOS\"\n    return 0\n");
    struct bytes nvfs = textf("nvfs-image-version=1\nplatform=%s\nlane=%s\n", platform, lane);
    struct bytes toolset = textf("lane = \"%s\"\nmode=native-filesystem-app\nstatus=standalone-required\n", lane);
    struct bytes simple_tool_manifest = textf(
        "[simple_toolchain]\nstatus = \"embedded\"\n"
        "host_payload = \"%s\"\nbuild_stamp = \"%s.build_stamp\"\n"
        "runtime_source = \"simpleos-filesystem\"\n"
        "role = \"/usr/bin/simple\"\nrole = \"/usr/bin/simple.smf\"\n"
        "role = \"/bin/simple\"\nrole = \"/bin/simple.smf\"\n"
        "role = \"/sys/apps/simple\"\nrole = \"/sys/apps/simple.smf\"\n"
        "role = \"/sys/apps/simple_compiler\"\nrole = \"/sys/apps/simple_compiler.smf\"\n"
        "role = \"/sys/apps/simple_interpreter\"\nrole = \"/sys/apps/simple_interpreter.smf\"\n"
        "role = \"/sys/apps/simple_loader\"\nrole = \"/sys/apps/simple_loader.smf\"\n",
        getenv("SIMPLEOS_SIMPLE_BINARY") ? getenv("SIMPLEOS_SIMPLE_BINARY") : "",
        getenv("SIMPLEOS_SIMPLE_BINARY") ? getenv("SIMPLEOS_SIMPLE_BINARY") : "");
    struct bytes markers = textf(
        "\nHELLOSMF\nBROWSMF\nSBROWSMF\nSMUXSMF\nSCOMPSMF\nSINTSMF\nSLOADSMF\nSIMPLSTC\nLLVMSMF\nCLANGSMF\nRUSTSMF\nSTEAM204SMF\n"
        "[steam-2048-demo] source=2048\n[game-port] profile=steamos-rebuild-v1 source=2048\nrebuild_target=simpleos-native\n"
        "steam_facade=simple-steam-sffi-v1\nport_required_capabilities=8\nruntime=SteamLinuxRuntime/soldier\nnetwork=true\nachievement=true\ndrm=true\n"
        "steam_backend_ready=false\nsteam_backend_blocker=missing_authenticated_steam_client\nsteam_backend_required_symbols=20\nsteam_backend_required_os_capabilities=11\n"
        "SMF\n/sys/apps/hello_world\n/sys/apps/simple_browser\n/sys/apps/smux\nSIMPLEOS_DISK_HELLO_ELF\nbrowser_demo_remote_main\nhello_world_remote_main\n"
        "file_manager_remote_main\nshell_remote_main\neditor_remote_main\nsmux_remote_main\ninfo|src/app/info/main.spl|smoke|staged\nlist|src/app/list/main.spl|smoke|staged\n"
        "stats|src/app/stats/main.spl|smoke|staged\nentry_app=/sys/apps/simple\nentry_app=/usr/bin/simple\nentry_app=/sys/apps/simple_compiler\nentry_app=/sys/apps/simple_interpreter\nentry_app=/sys/apps/simple_loader\nentry_app=/sys/apps/llvm\nentry_app=/sys/apps/clang\nentry_app=/sys/apps/rust\n"
        "lane=%s\nlane = \"%s\"\nelf-machine=%s\nmode=native-filesystem-app\nstatus=standalone-required\npipeline=compile-pipeline-step\npipeline=build-pipeline-step\n"
        "proof_pipeline=/usr/share/simpleos/toolchain/llvm/pipeline.step\nproof_pipeline=/usr/share/simpleos/toolchain/clang/pipeline.step\nproof_pipeline=/usr/share/simpleos/toolchain/rust/pipeline.step\n"
        "/usr/share/simpleos/toolchain/llvm/hello.ll\n/usr/bin/simple status=standalone-required\n/sys/apps/simple status=standalone-required\n/sys/apps/simple_compiler status=standalone-required\n/sys/apps/simple_interpreter status=standalone-required\n/sys/apps/simple_loader status=standalone-required\n/sys/apps/llvm status=standalone-required\n"
        "/sys/apps/clang status=standalone-required\n/sys/apps/rust status=standalone-required\nSimpleOS LLVM standalone app v1\nclang version 20.0.0\nSimpleOS Rust standalone app v1\n"
        "/usr/share/simpleos/toolchain/llvm/pipeline.step\n/usr/share/simpleos/toolchain/clang/pipeline.step\n/usr/share/simpleos/toolchain/rust/pipeline.step\n"
        "SIMPLEOS_FONT_ASSET_COUNT=16\nSIMPLEOS_FONT_BUNDLE_COUNT=53\nSIMPLEOS_FONT_ASSET_PATH=/SYS/FONTS/NOTOSANS\nSIMPLEOS_FONT_NOTICES_PATH=/SYS/FONTS/NOTICES.MD\n",
        lane, lane, platform);

    struct bytes llvm_manifest = textf("[toolchain]\napp=llvm\ntitle=LLVM\ntool=/sys/apps/llvm\nlane=%s\nmode=native-filesystem-app\nstatus=standalone-required\ncapability_primary=local-ir-inspection\nproof_primary=/usr/share/simpleos/toolchain/llvm/hello.ll\ncapability_secondary=object-assembly-inspection\nproof_secondary=/usr/share/simpleos/toolchain/llvm/hello.s\npipeline=compile-pipeline-step\nproof_pipeline=/usr/share/simpleos/toolchain/llvm/pipeline.step\n", lane);
    struct bytes clang_manifest = textf("[toolchain]\napp=clang\ntitle=Clang\ntool=/sys/apps/clang\nlane=%s\nmode=native-filesystem-app\nstatus=standalone-required\ncapability_primary=local-c-source-inspection\nproof_primary=/usr/share/simpleos/toolchain/clang/hello.c\ncapability_secondary=driver-flag-inspection\nproof_secondary=/usr/share/simpleos/toolchain/clang/flags.rsp\npipeline=compile-pipeline-step\nproof_pipeline=/usr/share/simpleos/toolchain/clang/pipeline.step\n", lane);
    struct bytes rust_manifest = textf("[toolchain]\napp=rust\ntitle=Rust\ntool=/sys/apps/rust\nlane=%s\nmode=native-filesystem-app\nstatus=standalone-required\ncapability_primary=local-source-inspection\nproof_primary=/usr/share/simpleos/toolchain/rust/hello.rs\ncapability_secondary=package-layout-inspection\nproof_secondary=/usr/share/simpleos/toolchain/rust/Cargo.toml\npipeline=build-pipeline-step\nproof_pipeline=/usr/share/simpleos/toolchain/rust/pipeline.step\n", lane);
    struct bytes steam_port = text_bytes("port_profile=steamos-rebuild-v1\napp_id=2048\napp_name=SimpleOS Steam 2048 Smoke\nsource=2048\nupstream=https://github.com/gabrielecirulli/2048\nlicense=MIT\nrebuild_target=simpleos-native\nruntime_profile=SteamLinuxRuntime/soldier-source-rebuild\npackage_path=/sys/apps/steam_2048\ngraphics_api=sdl2_subset\ninput_api=simple_input_events\naudio_api=simple_audio_optional\nnetwork_api=simple_bsd_sockets_optional\nstorage_api=simple_posix_save_data\nsteam_facade=simple-steam-sffi-v1\n");
    struct bytes llvm_ll = text_bytes("source_filename = \"hello.simple\"\ndefine i32 @main() { ret i32 0 }\n");
    struct bytes llvm_s = text_bytes(".globl _start\n_start:\n  ret\n");
    struct bytes llvm_pipe = text_bytes("pipeline=compile-pipeline-step\ninput=/work/hello.simple\noutput=/work/hello.ll\nnext=/sys/apps/simple_loader\n");
    struct bytes clang_c = text_bytes("#include <stdint.h>\nint main(void) { return 0; }\nconst char *msg = \"hello from simpleos clang\";\n");
    struct bytes clang_flags = text_bytes("-target x86_64-unknown-simpleos\n-ffreestanding\n-nostdlib\n");
    struct bytes clang_pipe = text_bytes("pipeline=compile-pipeline-step\ninput=/work/hello.c\noutput=/work/hello.o\nnext=/sys/apps/simple_loader\n");
    struct bytes rust_rs = text_bytes("#![no_std]\n#![no_main]\nfn main() {}\n");
    struct bytes rust_cargo = text_bytes("[package]\nname = \"simpleos-hello\"\nversion = \"0.1.0\"\nedition = \"2021\"\n");
    struct bytes rust_pipe = text_bytes("pipeline=build-pipeline-step\ninput=/work/Cargo.toml\noutput=/work/target/hello\nnext=/sys/apps/simple_loader\n");
    struct bytes fat4k = text_bytes("SIMPLEOS_FAT32_DIRECT_IO_4K_FIXTURE\n");

    struct bytes hello = smf(platform_elf(platform, hello_marker));
    struct bytes browser = smf(browser_payload.len ? browser_payload : platform_elf(platform, gui_marker));
    struct bytes simple_cli = simple_role_payload(platform, "SIMPLE", simple_payload);
    struct bytes simple_compiler = simple_role_payload(platform, "SIMPLE_COMPILER", simple_payload);
    struct bytes simple_interpreter = simple_role_payload(platform, "SIMPLE_INTERPRETER", simple_payload);
    struct bytes simple_loader = simple_role_payload(platform, "SIMPLE_LOADER", simple_payload);
    struct bytes llvm_app = app_elf(platform, "LLVM");
    struct bytes clang_app = app_elf(platform, "CLANG");
    struct bytes rust_app = app_elf(platform, "RUST");
    struct bytes steam_app = smf(platform_elf(platform, "[steam-2048-demo] source=2048 runtime=SteamLinuxRuntime/soldier network=true achievement=true drm=true"));

    int kernel_cluster = alloc_clusters(kernel.data, kernel.len);
    int bootloader_cluster = alloc_clusters(bootloader.data, bootloader.len);
    int limine_cluster = alloc_clusters(limine.data, limine.len);
    int hello_txt_cluster = alloc_clusters(hello_txt.data, hello_txt.len);
    int server_document_cluster = servers_payload.len ? alloc_clusters(server_document.data, server_document.len) : 0;
    int server_credential_cluster = servers_payload.len ? alloc_clusters(server_credential.data, server_credential.len) : 0;
    /* alloc_clusters copied the secret into the credential-bearing image.
     * Remove the transient host-side read buffer immediately; the resulting
     * image remains sensitive and is governed by the acceptance-image policy. */
    wipe_bytes(server_credential);
    int qemu_nonce_cluster = alloc_clusters(qemu_nonce_slot.data, qemu_nonce_slot.len);
    int collector_nonce_cluster = alloc_clusters(
        collector_nonce_slot.data, collector_nonce_slot.len);
    int numbers_cluster = alloc_clusters(numbers_txt.data, numbers_txt.len);
    int hello_spl_cluster = alloc_clusters(hello_spl.data, hello_spl.len);
    int nvfs_cluster = alloc_clusters(nvfs.data, nvfs.len);
    int toolset_cluster = alloc_clusters(toolset.data, toolset.len);
    int simple_tool_manifest_cluster = simple_payload.len ? alloc_clusters(simple_tool_manifest.data, simple_tool_manifest.len) : 0;
    int markers_cluster = alloc_clusters(markers.data, markers.len);
    int llvm_manifest_cluster = alloc_clusters(llvm_manifest.data, llvm_manifest.len);
    int clang_manifest_cluster = alloc_clusters(clang_manifest.data, clang_manifest.len);
    int rust_manifest_cluster = alloc_clusters(rust_manifest.data, rust_manifest.len);
    /* TODO(simpleos-steam-staging): a steam manifest and a proof marker were
     * once allocated here but never published into any directory — the clusters
     * were allocated in the FAT and orphaned (fsck "Reclaimed unused clusters").
     * The manifest named /usr/share/simpleos/games/steam_2048/marker.txt as its
     * proof_marker, so the intended staging path exists but was never wired.
     * The allocations are gone so the FAT stays consistent; the staging itself
     * is still owed. Do NOT re-add alloc_clusters here without also adding the
     * put_dir_entry that consumes it. */
    int steam_port_cluster = alloc_clusters(steam_port.data, steam_port.len);
    int llvm_ll_cluster = alloc_clusters(llvm_ll.data, llvm_ll.len);
    int llvm_s_cluster = alloc_clusters(llvm_s.data, llvm_s.len);
    int llvm_pipe_cluster = alloc_clusters(llvm_pipe.data, llvm_pipe.len);
    /* FAT32 has NO hard links: two directory entries must not share one cluster
     * chain. This payload is deliberately published at two paths (/SYS/CLANGHEL.C
     * via clang_c_cluster and /HELLO.C via hello_c_cluster), and sharing made
     * fsck report "/HELLO.C and /SYS/CLANGHEL.C share clusters. Truncating second
     * to 0 bytes" — one of the two paths then read as empty. Each path gets its
     * own independent copy. */
    int clang_c_cluster = alloc_clusters(clang_c.data, clang_c.len);
    int hello_c_cluster = alloc_clusters(clang_c.data, clang_c.len);
    int clang_flags_cluster = alloc_clusters(clang_flags.data, clang_flags.len);
    int clang_pipe_cluster = alloc_clusters(clang_pipe.data, clang_pipe.len);
    int rust_rs_cluster = alloc_clusters(rust_rs.data, rust_rs.len);
    int rust_cargo_cluster = alloc_clusters(rust_cargo.data, rust_cargo.len);
    int rust_pipe_cluster = alloc_clusters(rust_pipe.data, rust_pipe.len);
    int hello_cluster = alloc_clusters(hello.data, hello.len);
    int browser_cluster = alloc_clusters(browser.data, browser.len);
    int compiler_cluster = alloc_clusters(simple_compiler.data, simple_compiler.len);
    int interpreter_cluster = alloc_clusters(simple_interpreter.data, simple_interpreter.len);
    int loader_cluster = alloc_clusters(simple_loader.data, simple_loader.len);
    int simple_cluster = alloc_clusters(simple_cli.data, simple_cli.len);
    int simple_usr_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    /* Same no-hard-links rule as clang_c_cluster/hello_c_cluster above: this
     * payload is published at /USR/BIN/SIMPLE, /BIN/SIMPLE and /SIMPLE.ELF, so
     * each entry needs its own chain. Every allocation guard here must match the
     * guard on the CONSUMING put_dir_entry, or the chain is allocated in the FAT
     * and never referenced ("Reclaimed N unused clusters"). simple_usr_cluster is
     * non-zero exactly when simple_payload.len is non-zero (cluster numbers start
     * at 2), so the `if (simple_usr_cluster)` consumers below are covered by the
     * `simple_payload.len` guard used here; simple_root_cluster is consumed under
     * its own `if (simple_root_cluster)`. */
    int simple_bin_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_root_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_apps_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_usr_smf_cluster = simple_payload.len ? alloc_clusters(simple_cli.data, simple_cli.len) : 0;
    int simple_bin_smf_cluster = simple_payload.len ? alloc_clusters(simple_cli.data, simple_cli.len) : 0;
    int simple_compiler_raw_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_interpreter_raw_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int simple_loader_raw_cluster = simple_payload.len ? alloc_clusters(simple_payload.data, simple_payload.len) : 0;
    int clang_bin_cluster = clang_payload.len ? alloc_clusters(clang_payload.data, clang_payload.len) : 0;
    int llc_bin_cluster = llc_payload.len ? alloc_clusters(llc_payload.data, llc_payload.len) : 0;
    int lld_bin_cluster = lld_payload.len ? alloc_clusters(lld_payload.data, lld_payload.len) : 0;
    int crt0_cluster = crt0_payload.len ? alloc_clusters(crt0_payload.data, crt0_payload.len) : 0;
    int runtime_cluster = runtime_payload.len ? alloc_clusters(runtime_payload.data, runtime_payload.len) : 0;
    int libc_cluster = libc_payload.len ? alloc_clusters(libc_payload.data, libc_payload.len) : 0;
    int linker_script_cluster = linker_script_payload.len ? alloc_clusters(linker_script_payload.data, linker_script_payload.len) : 0;
    int simple_entry_cluster = simple_entry_payload.len ? alloc_clusters(simple_entry_payload.data, simple_entry_payload.len) : 0;
    int hello_object_cluster = hello_object_payload.len ? alloc_clusters(hello_object_payload.data, hello_object_payload.len) : 0;
    int hello_ir_cluster = hello_ir_payload.len ? alloc_clusters(hello_ir_payload.data, hello_ir_payload.len) : 0;
    int fsexec_cluster = fsexec_payload.len ? alloc_clusters(fsexec_payload.data, fsexec_payload.len) : 0;
    int servers_cluster = servers_payload.len ? alloc_clusters(servers_payload.data, servers_payload.len) : 0;
    int font_clusters[FONT_ASSET_COUNT];
    int font_metadata_clusters[FONT_ASSET_COUNT];
    int font_license_clusters[FONT_ASSET_COUNT];
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        font_clusters[i] = alloc_clusters(font_payloads[i].data, font_payloads[i].len);
        font_metadata_clusters[i] = alloc_clusters(font_metadata_payloads[i].data, font_metadata_payloads[i].len);
        font_license_clusters[i] = alloc_clusters(font_license_payloads[i].data, font_license_payloads[i].len);
    }
    int font_copyright_cluster = alloc_clusters(font_copyright_payload.data, font_copyright_payload.len);
    int font_corpus_cluster = alloc_clusters(font_corpus_payload.data, font_corpus_payload.len);
    int cldr_license_cluster = alloc_clusters(cldr_license_payload.data, cldr_license_payload.len);
    int simple_license_cluster = alloc_clusters(simple_license_payload.data, simple_license_payload.len);
    int third_party_notices_cluster = alloc_clusters(third_party_notices_payload.data, third_party_notices_payload.len);
    int llvm_cluster = alloc_clusters(llvm_app.data, llvm_app.len);
    int clang_cluster = alloc_clusters(clang_app.data, clang_app.len);
    int rust_cluster = alloc_clusters(rust_app.data, rust_app.len);
    int steam_cluster = alloc_clusters(steam_app.data, steam_app.len);
    int cfat4k_cluster = cfat4k.len ? alloc_clusters(cfat4k.data, cfat4k.len) : 0;
    int fat4k_cluster = alloc_clusters(fat4k.data, fat4k.len);
    int theme_cluster = theme_payload.len ? alloc_clusters(theme_payload.data, theme_payload.len) : 0;

    /* `tmp` was once the one directory given a cluster and a root entry but NO
     * content buffer, so its cluster was never written and fsck reported
     * "/TMP Expected a valid '.' entry in the first slot, found free entry".
     * Every directory declared here must also get dot entries below AND a
     * write_directory() call at the end — TMP was the sole gap. */
    unsigned char root[DIRECTORY_BYTES] = {0}, efi[DIRECTORY_BYTES] = {0};
    unsigned char boot[DIRECTORY_BYTES] = {0}, sys[DIRECTORY_BYTES] = {0};
    unsigned char fonts[DIRECTORY_BYTES] = {0}, apps[DIRECTORY_BYTES] = {0};
    unsigned char perf[DIRECTORY_BYTES] = {0}, usr[DIRECTORY_BYTES] = {0};
    unsigned char usr_bin[DIRECTORY_BYTES] = {0}, usr_lib[DIRECTORY_BYTES] = {0};
    unsigned char bin[DIRECTORY_BYTES] = {0}, sysrt[DIRECTORY_BYTES] = {0};
    unsigned char tmp[DIRECTORY_BYTES] = {0};
    int root_n = 0, efi_n = 0, boot_n = 0, sys_n = 0, fonts_n = 0;
    int apps_n = 0, perf_n = 0, usr_n = 0, usr_bin_n = 0, usr_lib_n = 0;
    int bin_n = 0, sysrt_n = 0, tmp_n = 0;
    put_dir_entry(root, &root_n, "SIMPLEOS   ", 0, 0, 0x08);
    put_dir_entry(root, &root_n, "EFI        ", efi_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "SYS        ", sys_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "USR        ", usr_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "BIN        ", bin_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "SYSRT      ", sysrt_cluster, 0, 0x10);
    put_dir_entry(root, &root_n, "TMP        ", tmp_cluster, 0, 0x10);
    if (theme_cluster)
        put_dir_entry(root, &root_n, "THEME   CSS", theme_cluster, theme_payload.len, 0x20);
    /* Lane BA: root-level staging of the cross-built interpreter so the arm64
     * board gate reads it via the proven root directory-scan path (avoids the
     * /SYS/APPS subdirectory descent). Placed early so the dirent stays within
     * the first 512-byte directory sector. */
    if (simple_root_cluster)
        put_dir_entry(root, &root_n, "SIMPLE  ELF", simple_root_cluster, simple_payload.len, 0x20);
    put_dir_entry(root, &root_n, "KERNEL  ELF", kernel_cluster, kernel.len, 0x20);
    put_dir_entry(root, &root_n, "LIMINE  CNF", limine_cluster, limine.len, 0x20);
    put_dir_entry(root, &root_n, "HELLO   TXT", hello_txt_cluster, hello_txt.len, 0x20);
    put_dir_entry(root, &root_n, "QEMUNONCTXT", qemu_nonce_cluster, qemu_nonce_slot.len, 0x20);
    put_dir_entry(root, &root_n, "SOSIXNONTXT", collector_nonce_cluster,
                  collector_nonce_slot.len, 0x20);
    put_dir_entry(root, &root_n, "NUMBERS TXT", numbers_cluster, numbers_txt.len, 0x20);
    put_dir_entry(root, &root_n, "HELLO   SPL", hello_spl_cluster, hello_spl.len, 0x20);
    put_dir_entry(root, &root_n, "HELLO   C  ", hello_c_cluster, clang_c.len, 0x20);
    if (hello_object_cluster)
        put_dir_entry(root, &root_n, "HELLO   O  ", hello_object_cluster, hello_object_payload.len, 0x20);
    if (hello_ir_cluster)
        put_dir_entry(root, &root_n, "HELLO   LL ", hello_ir_cluster, hello_ir_payload.len, 0x20);
    if (fsexec_cluster)
        put_dir_entry(root, &root_n, "FSEXEC  ELF", fsexec_cluster, fsexec_payload.len, 0x20);
    if (servers_cluster)
        put_dir_entry(root, &root_n, "SERVERS ELF", servers_cluster, servers_payload.len, 0x20);
    put_dot_entries(efi, &efi_n, efi_cluster, 0);
    put_dot_entries(boot, &boot_n, boot_cluster, efi_cluster);
    put_dot_entries(sys, &sys_n, sys_cluster, 0);
    put_dot_entries(fonts, &fonts_n, fonts_cluster, sys_cluster);
    put_dot_entries(apps, &apps_n, apps_cluster, sys_cluster);
    put_dot_entries(perf, &perf_n, perf_cluster, sys_cluster);
    put_dot_entries(usr, &usr_n, usr_cluster, 0);
    put_dot_entries(usr_bin, &usr_bin_n, usr_bin_cluster, usr_cluster);
    put_dot_entries(usr_lib, &usr_lib_n, usr_lib_cluster, usr_cluster);
    put_dot_entries(bin, &bin_n, bin_cluster, 0);
    put_dot_entries(sysrt, &sysrt_n, sysrt_cluster, 0);
    put_dot_entries(tmp, &tmp_n, tmp_cluster, 0);
    put_dir_entry(efi, &efi_n, "BOOT       ", boot_cluster, 0, 0x10);
    put_dir_entry(boot, &boot_n, "BOOTX64 EFI", bootloader_cluster, bootloader.len, 0x20);
    put_dir_entry(sys, &sys_n, "APPS       ", apps_cluster, 0, 0x10);
    put_dir_entry(sys, &sys_n, "PERF       ", perf_cluster, 0, 0x10);
    put_dir_entry(sys, &sys_n, "FONTS      ", fonts_cluster, 0, 0x10);
    if (servers_payload.len) {
        put_dir_entry(sys, &sys_n, "SERVER  HTM", server_document_cluster, server_document.len, 0x20);
        put_dir_entry(sys, &sys_n, "SRVDB   KEY", server_credential_cluster, server_credential.len, 0x20);
    }
    for (int i = 0; i < FONT_ASSET_COUNT; ++i) {
        put_named_dir_entry(fonts, &fonts_n, font_fat_names[i], font_long_names[i],
                            font_clusters[i], font_payloads[i].len, 0x20);
        char metadata_name[12], license_name[12];
        font_companion_fat_name(metadata_name, font_fat_names[i], "PB");
        font_companion_fat_name(license_name, font_fat_names[i], i == 12 ? "LIC" : "OFL");
        put_dir_entry(fonts, &fonts_n, metadata_name,
                      font_metadata_clusters[i], font_metadata_payloads[i].len, 0x20);
        put_dir_entry(fonts, &fonts_n, license_name,
                      font_license_clusters[i], font_license_payloads[i].len, 0x20);
    }
    char copyright_name[12];
    font_companion_fat_name(copyright_name, font_fat_names[12], "CPY");
    put_dir_entry(fonts, &fonts_n, copyright_name,
                  font_copyright_cluster, font_copyright_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "CORPUS  SDN",
                  font_corpus_cluster, font_corpus_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "CLDR    LIC",
                  cldr_license_cluster, cldr_license_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "SIMPLE  LIC",
                  simple_license_cluster, simple_license_payload.len, 0x20);
    put_dir_entry(fonts, &fonts_n, "NOTICES MD ",
                  third_party_notices_cluster, third_party_notices_payload.len, 0x20);
    /* 93 = 91 font-bundle entries + the 2 mandatory FAT32 dot entries. Guard
     * kept; only the expected total moved, by exactly 2. */
    if (fonts_n != 93)
        die("SimpleOS font bundle directory manifest mismatch");
    put_dir_entry(sys, &sys_n, "NVFSVER TXT", nvfs_cluster, nvfs.len, 0x20);
    put_dir_entry(sys, &sys_n, "TOOLSET SDN", toolset_cluster, toolset.len, 0x20);
    if (simple_tool_manifest_cluster)
        put_named_dir_entry(sys, &sys_n, "SIMPLETOSDN", "SIMPLETOOL.SDN",
                            simple_tool_manifest_cluster, simple_tool_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "MARKERS TXT", markers_cluster, markers.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVMMAN TXT", llvm_manifest_cluster, llvm_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGMANTXT", clang_manifest_cluster, clang_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTMAN TXT", rust_manifest_cluster, rust_manifest.len, 0x20);
    put_dir_entry(sys, &sys_n, "ST204PRTTXT", steam_port_cluster, steam_port.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVHELLOLL ", llvm_ll_cluster, llvm_ll.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVMPIPESTP", llvm_pipe_cluster, llvm_pipe.len, 0x20);
    put_dir_entry(sys, &sys_n, "LLVMHELLS  ", llvm_s_cluster, llvm_s.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGHELC  ", clang_c_cluster, clang_c.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGFLGRSP", clang_flags_cluster, clang_flags.len, 0x20);
    put_dir_entry(sys, &sys_n, "CLANGPLNSTP", clang_pipe_cluster, clang_pipe.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTHELORS ", rust_rs_cluster, rust_rs.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTCARGTOM", rust_cargo_cluster, rust_cargo.len, 0x20);
    put_dir_entry(sys, &sys_n, "RUSTPIPESTP", rust_pipe_cluster, rust_pipe.len, 0x20);
    put_dir_entry(apps, &apps_n, "HELLOSMFSMF", hello_cluster, hello.len, 0x20);
    put_dir_entry(apps, &apps_n, "BROWSMF SMF", browser_cluster, browser.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SCOMPSMFSMF", "simple_compiler.smf", compiler_cluster, simple_compiler.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SINTSMF SMF", "simple_interpreter.smf", interpreter_cluster, simple_interpreter.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SLOADSMFSMF", "simple_loader.smf", loader_cluster, simple_loader.len, 0x20);
    put_named_dir_entry(apps, &apps_n, "SIMPLSTCSMF", "simple.smf", simple_cluster, simple_cli.len, 0x20);
    put_dir_entry(usr, &usr_n, "BIN        ", usr_bin_cluster, 0, 0x10);
    put_dir_entry(usr, &usr_n, "LIB        ", usr_lib_cluster, 0, 0x10);
    if (simple_usr_cluster) {
        put_dir_entry(usr_bin, &usr_bin_n, "SIMPLE     ", simple_usr_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(usr_bin, &usr_bin_n, "SIMPLE  SMF", "simple.smf", simple_usr_smf_cluster, simple_cli.len, 0x20);
        put_dir_entry(bin, &bin_n, "SIMPLE     ", simple_bin_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(bin, &bin_n, "SIMPLE  SMF", "simple.smf", simple_bin_smf_cluster, simple_cli.len, 0x20);
        put_dir_entry(apps, &apps_n, "SIMPLE     ", simple_apps_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(apps, &apps_n, "SCOMPILER  ", "simple_compiler", simple_compiler_raw_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(apps, &apps_n, "SINTERP    ", "simple_interpreter", simple_interpreter_raw_cluster, simple_payload.len, 0x20);
        put_named_dir_entry(apps, &apps_n, "SLOADER    ", "simple_loader", simple_loader_raw_cluster, simple_payload.len, 0x20);
    }
    if (clang_bin_cluster)
        put_dir_entry(usr_bin, &usr_bin_n, "CLANG      ", clang_bin_cluster, clang_payload.len, 0x20);
    if (llc_bin_cluster)
        put_dir_entry(usr_bin, &usr_bin_n, "LLC        ", llc_bin_cluster, llc_payload.len, 0x20);
    if (lld_bin_cluster)
        put_dir_entry(usr_bin, &usr_bin_n, "LD      LLD", lld_bin_cluster, lld_payload.len, 0x20);
    if (crt0_cluster)
        put_dir_entry(usr_lib, &usr_lib_n, "CRT0    O  ", crt0_cluster, crt0_payload.len, 0x20);
    if (runtime_cluster)
        put_dir_entry(usr_lib, &usr_lib_n, "SIMPRT  A  ", runtime_cluster, runtime_payload.len, 0x20);
    if (libc_cluster)
        put_dir_entry(usr_lib, &usr_lib_n, "SOSLIB  A  ", libc_cluster, libc_payload.len, 0x20);
    if (simple_entry_cluster)
        put_dir_entry(usr_lib, &usr_lib_n, "SIMAIN  O  ", simple_entry_cluster, simple_entry_payload.len, 0x20);
    if (linker_script_cluster)
        put_dir_entry(sysrt, &sysrt_n, "SIMPLEOSLD ", linker_script_cluster, linker_script_payload.len, 0x20);
    put_dir_entry(apps, &apps_n, "LLVMSMF SMF", llvm_cluster, llvm_app.len, 0x20);
    put_dir_entry(apps, &apps_n, "CLANGSMFSMF", clang_cluster, clang_app.len, 0x20);
    put_dir_entry(apps, &apps_n, "RUSTSMF SMF", rust_cluster, rust_app.len, 0x20);
    put_dir_entry(apps, &apps_n, "STEAM204SMF", steam_cluster, steam_app.len, 0x20);
    if (cfat4k.len)
        put_dir_entry(perf, &perf_n, "CFAT4K  TXT", cfat4k_cluster, cfat4k.len, 0x20);
    put_dir_entry(perf, &perf_n, "FAT4K   BIN", fat4k_cluster, fat4k.len, 0x20);

    write_directory(ROOT_CLUSTER, root, root_n);
    write_directory(efi_cluster, efi, efi_n);
    write_directory(boot_cluster, boot, boot_n);
    write_directory(sys_cluster, sys, sys_n);
    write_directory(fonts_cluster, fonts, fonts_n);
    write_directory(apps_cluster, apps, apps_n);
    write_directory(perf_cluster, perf, perf_n);
    write_directory(usr_cluster, usr, usr_n);
    write_directory(usr_bin_cluster, usr_bin, usr_bin_n);
    write_directory(usr_lib_cluster, usr_lib, usr_lib_n);
    write_directory(bin_cluster, bin, bin_n);
    write_directory(sysrt_cluster, sysrt, sysrt_n);
    write_directory(tmp_cluster, tmp, tmp_n);

    finish_fat32_image(img_path);
    if (strcmp(platform, "x86_64") == 0 && bootloader_file.len)
        maybe_write_esp(img_path, &bootloader, &kernel, &limine);
    return 0;
}
