#define _GNU_SOURCE

#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <unistd.h>

static long now_us(void) {
    struct timeval tv;
    gettimeofday(&tv, 0);
    return tv.tv_sec * 1000000L + tv.tv_usec;
}

static int cmp_long(const void *a, const void *b) {
    long x = *(const long *)a;
    long y = *(const long *)b;
    return (x > y) - (x < y);
}

static long percentile(long *values, int count, int pct) {
    qsort(values, (size_t)count, sizeof(long), cmp_long);
    int idx = (count * pct) / 100;
    if (idx >= count) {
        idx = count - 1;
    }
    return values[idx];
}

static uint32_t read_u32_le(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

static void write_u32_le(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)v;
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
}

static long rand_block(long i, long block_count) {
    return ((i * 1103515245L + 12345L) & 0x7fffffffL) % block_count;
}

static int checked_pread(int fd, void *buf, size_t len, off_t off) {
    ssize_t got = pread(fd, buf, len, off);
    return got == (ssize_t)len ? 0 : -1;
}

static int checked_pwrite(int fd, const void *buf, size_t len, off_t off) {
    ssize_t wrote = pwrite(fd, buf, len, off);
    return wrote == (ssize_t)len ? 0 : -1;
}

static uint32_t follow_chain_to(int fd, long block_index) {
    uint8_t fat_sector[512];
    uint32_t cluster = 2;
    for (long i = 0; i < block_index; i++) {
        if (checked_pread(fd, fat_sector, sizeof(fat_sector), 32 * 512) != 0) {
            return 0;
        }
        cluster = read_u32_le(fat_sector + cluster * 4);
    }
    return cluster;
}

int main(void) {
    const char *path = "/tmp/cfat32_4k_baseline.img";
    const int blocks = 64;
    const int iters = 50;
    int fd = open(path, O_CREAT | O_RDWR | O_TRUNC, 0666);
    if (fd < 0) {
        perror("open");
        return 1;
    }
    if (ftruncate(fd, 4096 * 512) != 0) {
        perror("ftruncate");
        return 1;
    }

    uint8_t sector[512];
    memset(sector, 0, sizeof(sector));
    sector[11] = 0x00;
    sector[12] = 0x02;
    sector[13] = 0x08;
    sector[14] = 0x20;
    sector[16] = 0x02;
    write_u32_le(sector + 32, 4096);
    write_u32_le(sector + 36, 1);
    write_u32_le(sector + 44, 2);
    sector[510] = 0x55;
    sector[511] = 0xaa;
    if (checked_pwrite(fd, sector, sizeof(sector), 0) != 0) {
        perror("write bpb");
        return 1;
    }

    memset(sector, 0, sizeof(sector));
    write_u32_le(sector, 0x0ffffff8);
    write_u32_le(sector + 4, 0x0fffffff);
    for (int i = 0; i < blocks; i++) {
        write_u32_le(sector + 8 + i * 4, i == blocks - 1 ? 0x0ffffff8u : (uint32_t)(3 + i));
    }
    if (checked_pwrite(fd, sector, sizeof(sector), 32 * 512) != 0) {
        perror("write fat");
        return 1;
    }

    uint8_t block[4096];
    memset(block, 'A', sizeof(block));
    for (int i = 0; i < blocks; i++) {
        if (checked_pwrite(fd, block, sizeof(block), (40 + i * 8) * 512) != 0) {
            perror("seed data");
            return 1;
        }
    }

    long read_lat[50];
    long write_lat[50];
    for (int i = 0; i < iters; i++) {
        long b = rand_block(i, blocks);
        long t0 = now_us();
        uint32_t cluster = follow_chain_to(fd, b);
        if (cluster < 2 || checked_pread(fd, block, sizeof(block), (40 + (cluster - 2) * 8) * 512) != 0) {
            return 1;
        }
        read_lat[i] = now_us() - t0;
    }

    memset(block, 'W', sizeof(block));
    for (int i = 0; i < iters; i++) {
        long b = rand_block(i, blocks);
        long t0 = now_us();
        uint32_t cluster = follow_chain_to(fd, b);
        if (cluster < 2 || checked_pwrite(fd, block, sizeof(block), (40 + (cluster - 2) * 8) * 512) != 0) {
            return 1;
        }
        write_lat[i] = now_us() - t0;
    }

    printf("c_fat_direct_read4k: p50=%ldus p99=%ldus\n", percentile(read_lat, iters, 50), percentile(read_lat, iters, 99));
    printf("c_fat_direct_write4k: p50=%ldus p99=%ldus\n", percentile(write_lat, iters, 50), percentile(write_lat, iters, 99));
    long read_p99 = percentile(read_lat, iters, 99);
    long write_p99 = percentile(write_lat, iters, 99);
    long read_iops = read_p99 > 0 ? 1000000L / read_p99 : 1L;
    long write_iops = write_p99 > 0 ? 1000000L / write_p99 : 1L;
    printf("cfat4k_baseline c_read_iops=%ld c_write_iops=%ld c_read_p99_us=%ld c_write_p99_us=%ld\n",
           read_iops, write_iops, read_p99, write_p99);
    close(fd);
    return 0;
}
