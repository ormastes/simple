/**
 * @file direct_io.cu
 * @brief O_DIRECT implementation bypassing page cache
 *
 * Implements Direct I/O with proper alignment handling.
 * Requires aligned buffers and I/O sizes.
 */

#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <cstdio>
#include <cstring>
#include <chrono>
#include <algorithm>
// No CUDA-specific includes needed for Direct I/O

#define SECTOR_SIZE 4096  // Typical NVMe logical block size

struct IOStats {
    double throughput_gbs;
    double latency_us;
    size_t bytes_read;
};

/**
 * Check alignment requirements for O_DIRECT
 */
bool check_alignment(void* ptr, size_t size, size_t offset) {
    if (((uintptr_t)ptr % SECTOR_SIZE) != 0) {
        fprintf(stderr, "Buffer not aligned: %p (need %d-byte alignment)\n",
                ptr, SECTOR_SIZE);
        return false;
    }
    if ((size % SECTOR_SIZE) != 0) {
        fprintf(stderr, "Size not aligned: %zu (need %d-byte multiple)\n",
                size, SECTOR_SIZE);
        return false;
    }
    if ((offset % SECTOR_SIZE) != 0) {
        fprintf(stderr, "Offset not aligned: %zu (need %d-byte multiple)\n",
                offset, SECTOR_SIZE);
        return false;
    }
    return true;
}

/**
 * Direct I/O read with O_DIRECT flag
 */
IOStats direct_read_file(const char* path, size_t bytes) {
    // Align bytes to sector boundary
    size_t aligned_bytes = (bytes + SECTOR_SIZE - 1) & ~(SECTOR_SIZE - 1);

    // Allocate aligned buffer
    void* buffer = nullptr;
    if (posix_memalign(&buffer, SECTOR_SIZE, aligned_bytes) != 0) {
        perror("posix_memalign");
        return {0, 0, 0};
    }

    auto start = std::chrono::high_resolution_clock::now();

    int fd = open(path, O_RDONLY | O_DIRECT);
    if (fd < 0) {
        perror("open O_DIRECT");
        free(buffer);
        return {0, 0, 0};
    }

    size_t total_read = 0;
    ssize_t n;
    char* buf = static_cast<char*>(buffer);

    // Read in large chunks for better performance
    const size_t chunk_size = SECTOR_SIZE * 256;  // 1 MB chunks

    while (total_read < aligned_bytes) {
        size_t to_read = std::min(aligned_bytes - total_read, chunk_size);
        n = read(fd, buf + total_read, to_read);
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
    double throughput = (total_read / time_sec) / 1e9;

    free(buffer);
    return {throughput, duration.count(), total_read};
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

    printf("Direct I/O (O_DIRECT) Benchmark\n");
    printf("================================\n");
    printf("File: %s\n", path);
    printf("Size: %zu MB\n", size_mb);
    printf("Sector size: %d bytes\n\n", SECTOR_SIZE);

    // Test alignment check
    void* test_ptr;
    posix_memalign(&test_ptr, SECTOR_SIZE, SECTOR_SIZE);
    printf("Alignment check: %s\n\n",
           check_alignment(test_ptr, SECTOR_SIZE, 0) ? "PASS" : "FAIL");
    free(test_ptr);

    // Run benchmark
    printf("Reading with O_DIRECT:\n");
    IOStats stats = direct_read_file(path, bytes);

    printf("  Throughput: %.2f GB/s\n", stats.throughput_gbs);
    printf("  Time: %.2f ms\n", stats.latency_us / 1000.0);
    printf("  Bytes read: %zu\n", stats.bytes_read);

    printf("\nNote: O_DIRECT bypasses page cache, so performance is consistent\n");
    printf("      regardless of whether data is cached.\n");

    return 0;
}
