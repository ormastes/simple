#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

static int64_t now_micros(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000 + (int64_t)(ts.tv_nsec / 1000);
}

static const char *env_text(const char *key, const char *fallback) {
    const char *value = getenv(key);
    return value && value[0] ? value : fallback;
}

static int64_t env_i64(const char *key, int64_t fallback) {
    const char *value = getenv(key);
    return value && value[0] ? atoll(value) : fallback;
}

static int64_t file_size_or_die(const char *path) {
    struct stat st;
    if (stat(path, &st) != 0) {
        perror("stat");
        exit(2);
    }
    return (int64_t)st.st_size;
}

static void report(const char *case_name, int64_t bytes, int64_t iters, int64_t micros, int64_t checksum) {
    printf("[iobench] lang=c case=%s bytes=%lld iters=%lld micros=%lld checksum=%lld\n",
           case_name, (long long)bytes, (long long)iters, (long long)micros, (long long)checksum);
}

static void bench_read(const char *path, int64_t iters) {
    int64_t size = file_size_or_die(path);
    char *buf = malloc((size_t)size);
    if (!buf) {
        perror("malloc");
        exit(2);
    }
    int64_t checksum = 0;
    int64_t start = now_micros();
    for (int64_t i = 0; i < iters; i++) {
        int fd = open(path, O_RDONLY);
        if (fd < 0) {
            perror("open");
            exit(2);
        }
        int64_t off = 0;
        while (off < size) {
            ssize_t got = read(fd, buf + off, (size_t)(size - off));
            if (got <= 0) {
                perror("read");
                exit(2);
            }
            off += got;
        }
        close(fd);
        checksum += size;
    }
    int64_t elapsed = now_micros() - start;
    free(buf);
    report("read_text", checksum, iters, elapsed, checksum);
}

static void bench_mmap(const char *path, int64_t iters) {
    int64_t size = file_size_or_die(path);
    int64_t checksum = 0;
    int64_t start = now_micros();
    for (int64_t i = 0; i < iters; i++) {
        int fd = open(path, O_RDONLY);
        if (fd < 0) {
            perror("open");
            exit(2);
        }
        char *data = mmap(NULL, (size_t)size, PROT_READ, MAP_PRIVATE, fd, 0);
        if (data == MAP_FAILED) {
            perror("mmap");
            exit(2);
        }
        checksum += size;
        munmap(data, (size_t)size);
        close(fd);
    }
    int64_t elapsed = now_micros() - start;
    report("mmap_text", size * iters, iters, elapsed, checksum);
}

static void fill_chunk(char *chunk, size_t len) {
    static const char seed[] = "simple-io-parity-0123456789abcdef\n";
    for (size_t i = 0; i < len; i++) {
        chunk[i] = seed[i % (sizeof(seed) - 1)];
    }
}

static void bench_append_at(const char *path, int64_t iters) {
    char chunk[4096];
    fill_chunk(chunk, sizeof(chunk));
    unlink(path);
    int fd = open(path, O_CREAT | O_WRONLY, 0644);
    if (fd < 0) {
        perror("open write");
        exit(2);
    }
    int64_t checksum = 0;
    int64_t start = now_micros();
    for (int64_t i = 0; i < iters; i++) {
        ssize_t wrote = pwrite(fd, chunk, sizeof(chunk), i * (int64_t)sizeof(chunk));
        if (wrote != (ssize_t)sizeof(chunk)) {
            perror("pwrite");
            exit(2);
        }
        checksum += wrote;
    }
    int64_t elapsed = now_micros() - start;
    close(fd);
    report("append_at", file_size_or_die(path), iters, elapsed, checksum);
}

int main(void) {
    const char *fixture = env_text("IO_PARITY_FIXTURE", "build/perf/io_parity/fixture.txt");
    const char *output = env_text("IO_PARITY_OUTPUT", "build/perf/io_parity/c_append.out");
    int64_t iters = env_i64("IO_PARITY_ITERS", 64);
    bench_read(fixture, iters);
    bench_mmap(fixture, iters);
    bench_append_at(output, iters);
    return 0;
}
