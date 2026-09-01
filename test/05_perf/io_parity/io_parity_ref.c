#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

int io_contract_ok(int open_ok, int missing_rejected, long partial_len,
                   long eof_len, int exact_ok, int exact_short_rejected);

static int64_t checksum_bytes(const unsigned char *bytes, size_t len) {
    int64_t sum = 0;
    for (size_t i = 0; i < len; ++i)
        sum = (sum + bytes[i]) % 2147483647;
    return sum;
}

static int64_t positive_i64_or(const char *raw, int64_t fallback) {
    if (!raw || !*raw) return fallback;
    int64_t value = 0;
    for (const unsigned char *p = (const unsigned char *)raw; *p; ++p) {
        if (*p < '0' || *p > '9') return fallback;
        value = value * 10 + (*p - '0');
    }
    return value > 0 ? value : fallback;
}

static int64_t file_size_or_error(const char *path) {
    struct stat st;
    if (stat(path, &st) != 0) return -1;
    return (int64_t)st.st_size;
}

static int read_all_exact(int fd, unsigned char *buf, size_t size) {
    size_t offset = 0;
    while (offset < size) {
        ssize_t got = read(fd, buf + offset, size - offset);
        if (got > 0) offset += (size_t)got;
        else if (got < 0 && errno == EINTR) continue;
        else return 0;
    }
    return 1;
}

static int pwrite_all_exact(int fd, const unsigned char *buf, size_t size,
                            int64_t base_offset) {
    size_t offset = 0;
    while (offset < size) {
        ssize_t wrote = pwrite(fd, buf + offset, size - offset,
                               (off_t)(base_offset + (int64_t)offset));
        if (wrote > 0) offset += (size_t)wrote;
        else if (wrote < 0 && errno == EINTR) continue;
        else return 0;
    }
    return 1;
}

static void report(const char *case_name, int64_t bytes, int64_t iters,
                   int64_t checksum) {
    printf("[iobench-observation] lang=c case=%s bytes=%lld iters=%lld checksum=%lld\n",
           case_name, (long long)bytes, (long long)iters, (long long)checksum);
}

static int contract(const char *path, const char *missing) {
    int missing_fd = open(missing, O_RDONLY);
    int missing_rejected = missing_fd < 0;
    if (missing_fd >= 0) close(missing_fd);
    int fd = open(path, O_RDONLY);
    if (fd < 0) { puts("[iobench-contract] lang=c status=fail reason=open"); return 1; }
    unsigned char buf[17];
    ssize_t partial = read(fd, buf, sizeof buf);
    ssize_t eof = read(fd, buf, 1);
    int open_ok = partial == 11 && checksum_bytes(buf, 11) == 1122;
    int close_ok = close(fd) == 0;
    fd = open(path, O_RDONLY);
    if (fd < 0) return 1;
    ssize_t exact_len = read(fd, buf, 11);
    int exact_ok = exact_len == 11;
    int exact_close_ok = close(fd) == 0;
    fd = open(path, O_RDONLY);
    if (fd < 0) return 1;
    ssize_t short_len = read(fd, buf, sizeof buf);
    int exact_short_rejected = short_len != (ssize_t)sizeof buf;
    int short_close_ok = close(fd) == 0;
    if (io_contract_ok(open_ok, missing_rejected, partial, eof, exact_ok,
                       exact_short_rejected) && close_ok && exact_close_ok && short_close_ok) {
        puts("[iobench-contract] lang=c status=pass partial=11 eof=0 checksum=1122 exact=pass exact_short=rejected missing=rejected");
        return 0;
    }
    puts("[iobench-contract] lang=c status=fail reason=observation");
    return 1;
}

static int bench_read_text(const char *path, int64_t iterations) {
    int64_t size = file_size_or_error(path);
    if (size < 0) return 1;
    int64_t total_bytes = 0, checksum = 0;
    for (int64_t iteration = 0; iteration < iterations; ++iteration) {
        int fd = open(path, O_RDONLY);
        unsigned char *buf = malloc((size_t)size);
        if (fd < 0 || !buf || !read_all_exact(fd, buf, (size_t)size)) {
            if (fd >= 0) close(fd);
            free(buf);
            return 1;
        }
        if (close(fd) != 0) { free(buf); return 1; }
        total_bytes += size;
        checksum = (checksum + checksum_bytes(buf, (size_t)size)) % 2147483647;
        free(buf);
    }
    report("read_text", total_bytes, iterations, checksum);
    return 0;
}

static int bench_mmap_text(const char *path, int64_t iterations) {
    int64_t size = file_size_or_error(path);
    if (size <= 0) return 1;
    int64_t total_bytes = 0, checksum = 0;
    for (int64_t iteration = 0; iteration < iterations; ++iteration) {
        int fd = open(path, O_RDONLY);
        if (fd < 0) return 1;
        unsigned char *mapped = mmap(NULL, (size_t)size, PROT_READ, MAP_PRIVATE, fd, 0);
        if (mapped == MAP_FAILED) { close(fd); return 1; }
        unsigned char *text_copy = malloc((size_t)size);
        if (!text_copy) { munmap(mapped, (size_t)size); close(fd); return 1; }
        memcpy(text_copy, mapped, (size_t)size);
        total_bytes += size;
        checksum = (checksum + checksum_bytes(text_copy, (size_t)size)) % 2147483647;
        free(text_copy);
        if (munmap(mapped, (size_t)size) != 0 || close(fd) != 0) return 1;
    }
    report("mmap_text", total_bytes, iterations, checksum);
    return 0;
}

static void fill_chunk(unsigned char *chunk, size_t len) {
    static const unsigned char seed[] = "simple-io-parity-0123456789abcdef\n";
    for (size_t i = 0; i < len; ++i) chunk[i] = seed[i % (sizeof seed - 1)];
}

static int bench_append_at(const char *path, int64_t iterations) {
    unsigned char chunk[4096];
    fill_chunk(chunk, sizeof chunk);
    int fd = open(path, O_CREAT | O_TRUNC | O_WRONLY, 0644);
    if (fd < 0) return 1;
    int64_t total_bytes = 0, checksum = 0;
    int64_t chunk_checksum = checksum_bytes(chunk, sizeof chunk);
    for (int64_t iteration = 0; iteration < iterations; ++iteration) {
        if (!pwrite_all_exact(fd, chunk, sizeof chunk, total_bytes)) { close(fd); return 1; }
        total_bytes += (int64_t)sizeof chunk;
        checksum = (checksum + chunk_checksum) % 2147483647;
    }
    if (close(fd) != 0) return 1;
    report("append_at", total_bytes, iterations, checksum);
    return 0;
}

int main(void) {
    const char *root = getenv("IO_PARITY_ROOT");
    const char *mode = getenv("IO_PARITY_MODE");
    if (!root || !*root || !mode || !*mode) return 2;
    char path[4096], missing[4096];
    if (strcmp(mode, "contract") == 0) {
        if (snprintf(path, sizeof path, "%s/contract.bin", root) >= (int)sizeof path ||
            snprintf(missing, sizeof missing, "%s/missing.bin", root) >= (int)sizeof missing)
            return 2;
        return contract(path, missing);
    }
    int64_t iterations = positive_i64_or(getenv("IO_PARITY_ITERS"), 8);
    if (strcmp(mode, "append_at") == 0) {
        const char *output = getenv("IO_PARITY_OUTPUT");
        return output && *output ? bench_append_at(output, iterations) : 2;
    }
    if (snprintf(path, sizeof path, "%s/payload.bin", root) >= (int)sizeof path) return 2;
    if (strcmp(mode, "read_text") == 0) return bench_read_text(path, iterations);
    if (strcmp(mode, "mmap_text") == 0) return bench_mmap_text(path, iterations);
    return 2;
}
