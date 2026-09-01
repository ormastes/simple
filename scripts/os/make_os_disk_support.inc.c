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

/* Read a security-sensitive build input only after proving that its size is
 * bounded.  The generic image inputs predate this contract and may be large;
 * server credentials must never be allocated from an attacker-controlled
 * length before their limits are checked. */
static struct bytes read_bounded_regular_file(const char *path, size_t max_len)
{
    struct bytes out = {0};
#ifdef _WIN32
    /* Windows hosted builds retain the generic image writer, but server-secret
     * staging stays disabled until a CreateFile/reparse-point owner provides
     * the same descriptor contract as O_NOFOLLOW+fstat below. */
    (void)path;
    (void)max_len;
    return out;
#else
    struct stat metadata;
    if (!path || path[0] == '\0')
        return out;
    int descriptor = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (descriptor < 0 || fstat(descriptor, &metadata) != 0 ||
        !S_ISREG(metadata.st_mode) || metadata.st_size <= 0 ||
        (metadata.st_mode & (S_IRWXG | S_IRWXO)) != 0 ||
        (uintmax_t)metadata.st_size > (uintmax_t)max_len) {
        if (descriptor >= 0)
            close(descriptor);
        return out;
    }
    size_t expected = (size_t)metadata.st_size;
    out.len = expected;
    out.data = (unsigned char *)xcalloc(out.len + 1, 1);
    size_t read_total = 0;
    while (read_total < expected) {
        ssize_t count = read(descriptor, out.data + read_total, expected - read_total);
        if (count <= 0)
            break;
        read_total += (size_t)count;
    }
    unsigned char extra = 0;
    ssize_t extra_count = read(descriptor, &extra, 1);
    if (read_total != expected || extra_count != 0 ||
        fstat(descriptor, &metadata) != 0 || (size_t)metadata.st_size != expected) {
        wipe_bytes(out);
        free(out.data);
        out.data = NULL;
        out.len = 0;
    }
    close(descriptor);
    return out;
#endif
}

static void require_cluster_bytes(int first_cluster, const struct bytes expected,
                                  const char *label)
{
    size_t consumed = 0;
    int cluster = first_cluster;
    while (consumed < expected.len) {
        size_t chunk = expected.len - consumed;
        if (chunk > g_cluster_size)
            chunk = g_cluster_size;
        if (memcmp(g_image + cluster_offset(cluster), expected.data + consumed, chunk) != 0)
            die(label);
        consumed += chunk;
        cluster = (int)g_fat[cluster];
    }
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
