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

static int env_case_is(const char *expected) {
    const char *actual = getenv("IO_PARITY_CASE");
    return actual && strcmp(actual, expected) == 0;
}

static void fail_case(const char *reason) {
    fprintf(stderr, "[iobench-error] lang=c reason=%s\n", reason);
    exit(2);
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
    printf("[iobench] lang=c engine=c-native case=%s bytes=%lld iters=%lld micros=%lld checksum=%lld\n",
           case_name, (long long)bytes, (long long)iters, (long long)micros, (long long)checksum);
}

static int64_t byte_checksum(const unsigned char *data, size_t len) {
    int64_t checksum = 0;
    for (size_t i = 0; i < len; i++) {
        checksum += data[i];
    }
    return checksum;
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
        char *data = mmap(NULL, (size_t)size, PROT_READ, MAP_SHARED, fd, 0);
        if (data == MAP_FAILED) {
            perror("mmap");
            exit(2);
        }
        close(fd);
        checksum += byte_checksum((const unsigned char *)data, (size_t)size);
        if (munmap(data, (size_t)size) != 0) {
            fail_case("munmap_failed");
        }
    }
    int64_t elapsed = now_micros() - start;
    report("mmap_direct", size * iters, iters, elapsed, checksum);
}

static void fill_chunk(char *chunk, size_t len) {
    static const char seed[] = "simple-io-parity-0123456789abcdef\n";
    for (size_t i = 0; i < len; i++) {
        chunk[i] = seed[i % (sizeof(seed) - 1)];
    }
}

static int write_all_at(int fd, const unsigned char *data, size_t len, int64_t offset) {
    size_t written = 0;
    while (written < len) {
        ssize_t rc = pwrite(fd, data + written, len - written, offset + (int64_t)written);
        if (rc <= 0) {
            if (rc == 0) {
                errno = EIO;
            }
            return 0;
        }
        written += (size_t)rc;
    }
    return 1;
}

static void bench_append_at(const char *path, int64_t iters) {
    char chunk[4096];
    fill_chunk(chunk, sizeof(chunk));
    int64_t expected_size = iters * (int64_t)sizeof(chunk);
    if (file_size_or_die(path) != expected_size) {
        fprintf(stderr, "precreated append target has wrong size\n");
        exit(2);
    }
    int64_t expected_checksum = byte_checksum((const unsigned char *)chunk, sizeof(chunk)) * iters;
    int64_t start = now_micros();
    for (int64_t i = 0; i < iters; i++) {
        int fd = open(path, O_WRONLY);
        if (fd < 0) {
            perror("open write iteration");
            exit(2);
        }
        if (!write_all_at(fd, (const unsigned char *)chunk, sizeof(chunk), i * (int64_t)sizeof(chunk))) {
            perror("pwrite");
            exit(2);
        }
        close(fd);
    }
    int64_t elapsed = now_micros() - start;
    report("append_at", expected_size, iters, elapsed, expected_checksum);
}

int main(void) {
    const char *fixture = env_text("IO_PARITY_FIXTURE", "build/perf/io_parity/fixture.txt");
    const char *output = env_text("IO_PARITY_OUTPUT", "build/perf/io_parity/c_append.out");
    int64_t iters = env_i64("IO_PARITY_ITERS", 64);
    if (iters <= 0) {
        fail_case("invalid_iterations");
    }
    if (env_case_is("mmap_direct")) {
        bench_mmap(fixture, iters);
    } else if (env_case_is("append_at")) {
        bench_append_at(output, iters);
    } else {
        fail_case("unknown_case");
    }
    return 0;
}
