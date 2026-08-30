#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

static volatile uint64_t warm_sink;

static int checksum_mapping(int fd, size_t size, uint64_t *checksum_out) {
    unsigned char *data = mmap(NULL, size, PROT_READ, MAP_SHARED, fd, 0);
    if (data == MAP_FAILED) {
        perror("cache-control mmap");
        return 2;
    }
    uint64_t checksum = 0;
    for (size_t i = 0; i < size; i++) {
        checksum += data[i];
    }
    *checksum_out = checksum;
    if (munmap(data, size) != 0) {
        perror("cache-control munmap");
        return 2;
    }
    return 0;
}

static int prepare_output(const char *path, off_t size) {
    int fd = open(path, O_CREAT | O_RDWR | O_TRUNC, 0644);
    if (fd < 0) {
        perror("cache-control prepare open");
        return 2;
    }
    int rc = 0;
    if (size <= 0 || ftruncate(fd, size) != 0) {
        perror("cache-control prepare truncate");
        rc = 2;
    }
    close(fd);
    return rc;
}

int main(int argc, char **argv) {
    if (argc == 4 && strcmp(argv[2], "prepare") == 0) {
        return prepare_output(argv[1], (off_t)atoll(argv[3]));
    }
    if (argc != 3 && argc != 5) {
        fprintf(stderr, "usage: %s FILE cold|warm | FILE prepare BYTES | FILE verify BYTES CHECKSUM\n", argv[0]);
        return 2;
    }
    if (argc == 5 && strcmp(argv[2], "verify") != 0) {
        fprintf(stderr, "cache-control invalid verification mode\n");
        return 2;
    }
    if (argc == 3 && strcmp(argv[2], "cold") != 0 && strcmp(argv[2], "warm") != 0) {
        fprintf(stderr, "cache-control invalid cache mode\n");
        return 2;
    }
    int fd = open(argv[1], O_RDONLY);
    if (fd < 0) {
        perror("cache-control open");
        return 2;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size <= 0) {
        perror("cache-control fstat");
        close(fd);
        return 2;
    }
    int rc = 0;
    if (strcmp(argv[2], "verify") == 0) {
        uint64_t expected_size = strtoull(argv[3], NULL, 10);
        uint64_t expected_checksum = strtoull(argv[4], NULL, 10);
        uint64_t actual_checksum = 0;
        if ((uint64_t)st.st_size != expected_size || checksum_mapping(fd, (size_t)st.st_size, &actual_checksum) != 0 ||
            actual_checksum != expected_checksum) {
            fprintf(stderr, "cache-control verify mismatch bytes=%lld checksum=%llu\n",
                    (long long)st.st_size, (unsigned long long)actual_checksum);
            rc = 2;
        } else {
            printf("bytes=%lld checksum=%llu\n", (long long)st.st_size, (unsigned long long)actual_checksum);
        }
    } else if (strcmp(argv[2], "cold") == 0) {
        rc = posix_fadvise(fd, 0, st.st_size, POSIX_FADV_DONTNEED);
        if (rc != 0) {
            errno = rc;
            perror("cache-control posix_fadvise");
            rc = 2;
        }
    } else {
        uint64_t checksum = 0;
        rc = checksum_mapping(fd, (size_t)st.st_size, &checksum);
        warm_sink = checksum;
    }
    close(fd);
    return rc;
}
