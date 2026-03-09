/**
 * @file posix_io.cu
 * @brief Standard POSIX I/O baseline implementation
 *
 * This file implements basic POSIX read/write operations as a baseline
 * for comparing with more advanced I/O methods.
 */

#include <fcntl.h>
#include <unistd.h>
#include <cstdio>
#include <cstring>
#include <chrono>
// No CUDA-specific includes needed for POSIX I/O

struct IOStats {
    double throughput_gbs;
    double latency_us;
    size_t bytes_read;
};

/**
 * Standard POSIX read
 * Goes through kernel page cache
 */
IOStats posix_read_file(const char* path, void* buffer, size_t bytes) {
    auto start = std::chrono::high_resolution_clock::now();

    int fd = open(path, O_RDONLY);
    if (fd < 0) {
        perror("open");
        return {0, 0, 0};
    }

    size_t total_read = 0;
    ssize_t n;
    char* buf = static_cast<char*>(buffer);

    while (total_read < bytes) {
        n = read(fd, buf + total_read, bytes - total_read);
        if (n <= 0) {
            if (n < 0) perror("read");
            break;
        }
        total_read += n;
    }

    close(fd);

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double, std::micro> duration = end - start;

    double time_sec = duration.count() / 1e6;
    double throughput = (total_read / time_sec) / 1e9;  // GB/s

    return {throughput, duration.count(), total_read};
}

/**
 * Drop Linux page cache (requires root)
 */
void drop_page_cache() {
    int fd = open("/proc/sys/vm/drop_caches", O_WRONLY);
    if (fd < 0) {
        perror("drop_caches (need root)");
        return;
    }
    write(fd, "3\n", 2);
    close(fd);
}

/**
 * Main test program
 */
int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <file_path> [size_mb]\n", argv[0]);
        return 1;
    }

    const char* path = argv[1];
    size_t size_mb = (argc > 2) ? atoi(argv[2]) : 100;
    size_t bytes = size_mb * 1024 * 1024;

    // Allocate buffer
    void* buffer = malloc(bytes);
    if (!buffer) {
        perror("malloc");
        return 1;
    }

    printf("POSIX I/O Benchmark\n");
    printf("===================\n");
    printf("File: %s\n", path);
    printf("Size: %zu MB\n\n", size_mb);

    // Cold cache test
    printf("Cold cache (first read):\n");
    drop_page_cache();
    sleep(1);

    IOStats cold = posix_read_file(path, buffer, bytes);
    printf("  Throughput: %.2f GB/s\n", cold.throughput_gbs);
    printf("  Time: %.2f ms\n", cold.latency_us / 1000.0);
    printf("  Bytes read: %zu\n\n", cold.bytes_read);

    // Warm cache test
    printf("Warm cache (second read):\n");
    IOStats warm = posix_read_file(path, buffer, bytes);
    printf("  Throughput: %.2f GB/s\n", warm.throughput_gbs);
    printf("  Time: %.2f ms\n", warm.latency_us / 1000.0);
    printf("  Bytes read: %zu\n\n", warm.bytes_read);

    printf("Speedup (warm/cold): %.2fx\n", warm.throughput_gbs / cold.throughput_gbs);

    free(buffer);
    return 0;
}
