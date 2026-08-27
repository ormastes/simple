#include <stdint.h>
#include <stdio.h>

#define VIRTIO_VENDOR UINT64_C(0x1af4)
#define NET_LEGACY UINT64_C(0x1000)
#define NET_MODERN UINT64_C(0x1041)
#define BLK_LEGACY UINT64_C(0x1001)
#define BLK_MODERN UINT64_C(0x1042)
#define GPU_LEGACY UINT64_C(0x1010)
#define GPU_MODERN UINT64_C(0x1050)
#define INPUT_LEGACY UINT64_C(0x1012)
#define INPUT_MODERN UINT64_C(0x1052)

typedef struct {
    uint64_t count;
    uint64_t hash1;
    uint64_t hash2;
} Digest;

static uint64_t rotate_left(uint64_t value, unsigned shift) {
    return (value << shift) | (value >> (64U - shift));
}

static void digest_reset(Digest *digest) {
    digest->count = 0;
    digest->hash1 = UINT64_C(0x243f6a8885a308d3);
    digest->hash2 = UINT64_C(0x13198a2e03707344);
}

static void digest_add(Digest *digest, uint64_t value) {
    uint64_t index = digest->count;
    digest->hash1 = (digest->hash1 ^ value ^ index) * UINT64_C(1099511628211);
    digest->hash2 = (digest->hash2 + rotate_left(value, 31) +
        index * UINT64_C(0x9e3779b97f4a7c15)) * UINT64_C(14029467366897019727);
    digest->count++;
}

static void digest_emit(const char *case_id, const Digest *digest) {
    printf("%s count=%llu hash1=%llu hash2=%llu\n", case_id,
           (unsigned long long)digest->count,
           (unsigned long long)digest->hash1,
           (unsigned long long)digest->hash2);
}

static uint16_t ref_be16(const uint8_t *p) {
    return (uint16_t)(((uint16_t)p[0] << 8) | (uint16_t)p[1]);
}

static uint32_t ref_be32(const uint8_t *p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) |
        ((uint32_t)p[2] << 8) | (uint32_t)p[3];
}

static void ref_put_be16(uint8_t *p, uint16_t value) {
    p[0] = (uint8_t)(value >> 8);
    p[1] = (uint8_t)value;
}

static void ref_put_be32(uint8_t *p, uint32_t value) {
    p[0] = (uint8_t)(value >> 24);
    p[1] = (uint8_t)(value >> 16);
    p[2] = (uint8_t)(value >> 8);
    p[3] = (uint8_t)value;
}

static uint32_t ref_checksum_add(uint32_t sum, const uint8_t *data, uint64_t len) {
    uint64_t i = 0;
    while (i + 1 < len) {
        sum += ((uint32_t)data[i] << 8) | (uint32_t)data[i + 1];
        i += 2;
    }
    if (i < len) {
        sum += (uint32_t)data[i] << 8;
    }
    return sum;
}

static uint16_t ref_checksum_finish(uint32_t sum) {
    while (sum >> 16) {
        sum = (sum & UINT32_C(0xffff)) + (sum >> 16);
    }
    return (uint16_t)(~sum);
}

static int64_t ref_virtio_net(int64_t cls, int64_t sub, int64_t vendor,
                              int64_t device_id) {
    if (cls != 2 || sub != 0) return 0;
    if ((uint64_t)vendor != VIRTIO_VENDOR) return 0;
    if ((uint64_t)device_id == NET_LEGACY ||
        (uint64_t)device_id == NET_MODERN) return 1;
    return 0;
}

static int64_t ref_virtio_gpu(int64_t cls, int64_t sub, int64_t vendor,
                              int64_t device_id) {
    if ((uint64_t)vendor != VIRTIO_VENDOR) return 0;
    if ((uint64_t)device_id == GPU_LEGACY) return 1;
    if ((uint64_t)device_id == GPU_MODERN) {
        (void)cls;
        (void)sub;
        return 1;
    }
    return 0;
}

static int64_t ref_virtio_blk(int64_t vendor, int64_t device_id) {
    if ((uint64_t)vendor != VIRTIO_VENDOR) return 0;
    if ((uint64_t)device_id == BLK_LEGACY ||
        (uint64_t)device_id == BLK_MODERN) return 1;
    return 0;
}

static int64_t ref_virtio_input(int64_t vendor, int64_t device_id) {
    return (uint64_t)vendor == VIRTIO_VENDOR &&
        ((uint64_t)device_id == INPUT_LEGACY ||
         (uint64_t)device_id == INPUT_MODERN);
}

static void ref_put_le32(uint8_t *p, uint32_t value) {
    p[0] = (uint8_t)value;
    p[1] = (uint8_t)(value >> 8);
    p[2] = (uint8_t)(value >> 16);
    p[3] = (uint8_t)(value >> 24);
}

static void ref_put_le64(uint8_t *p, uint64_t value) {
    for (uint64_t i = 0; i < 8; i++) {
        p[i] = (uint8_t)(value >> (i * 8));
    }
}

static uint32_t ref_get_le32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
        ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

int main(void) {
    uint8_t raw[128] = {0};
    Digest digest;
    uint64_t total_cases = 0;

    digest_reset(&digest);
    for (uint64_t a = 0; a < 256; a++) {
        for (uint64_t b = 0; b < 256; b++) {
            raw[0] = (uint8_t)a;
            raw[1] = (uint8_t)b;
            digest_add(&digest, ref_be16(raw));
        }
    }
    digest_emit("be16-read-exhaustive", &digest);
    total_cases += digest.count;

    digest_reset(&digest);
    for (uint64_t value = 0; value < 65536; value++) {
        ref_put_be16(raw, (uint16_t)value);
        digest_add(&digest, ((uint64_t)raw[0] << 8) | raw[1]);
    }
    digest_emit("be16-write-exhaustive", &digest);
    total_cases += digest.count;

    digest_reset(&digest);
    for (uint64_t index = 0; index < 65536; index++) {
        raw[0] = (uint8_t)(index >> 8);
        raw[1] = (uint8_t)index;
        raw[2] = (uint8_t)((~index) >> 8);
        raw[3] = (uint8_t)(~index);
        digest_add(&digest, ref_be32(raw));
    }
    digest_emit("be32-read-grid", &digest);
    total_cases += digest.count;

    digest_reset(&digest);
    for (uint64_t index = 0; index < 65536; index++) {
        uint32_t word = (uint32_t)index * UINT32_C(0x00010001) ^
            UINT32_C(0xa5a55a5a);
        ref_put_be32(raw, word);
        digest_add(&digest, ((uint64_t)raw[0] << 24) |
                   ((uint64_t)raw[1] << 16) |
                   ((uint64_t)raw[2] << 8) | raw[3]);
    }
    digest_emit("be32-write-grid", &digest);
    total_cases += digest.count;

    digest_reset(&digest);
    for (uint64_t index = 0; index < 65536; index++) {
        uint32_t word = (uint32_t)index * UINT32_C(0x00010001) ^
            UINT32_C(0x5aa5a55a);
        ref_put_le32(raw, word);
        uint64_t bytes = (uint64_t)raw[0] | ((uint64_t)raw[1] << 8) |
            ((uint64_t)raw[2] << 16) | ((uint64_t)raw[3] << 24);
        uint64_t round_trip = ref_get_le32(raw);
        digest_add(&digest, bytes ^ rotate_left(round_trip, 11));
    }
    digest_emit("le32-write-read-grid", &digest);
    total_cases += digest.count;

    digest_reset(&digest);
    for (uint64_t index = 0; index < 65536; index++) {
        uint64_t word = (index << 48) | (index << 16) | ((~index) & 0xffff);
        uint64_t observed = 0;
        ref_put_le64(raw, word);
        for (uint64_t byte_index = 0; byte_index < 8; byte_index++) {
            observed |= (uint64_t)raw[byte_index] << (byte_index * 8);
        }
        digest_add(&digest, observed);
    }
    digest_emit("le64-write-grid", &digest);
    total_cases += digest.count;

    static const uint32_t seeds[] = {
        0, 1, 0xffff, 0x10000, 0xffff0000, 0x7fffffff, 0x80000000, 0xffffffff
    };
    digest_reset(&digest);
    for (uint64_t pattern = 0; pattern < 4; pattern++) {
        for (uint64_t i = 0; i < 66; i++) {
            raw[i] = (uint8_t)(i * 17 + pattern * 29);
        }
        for (uint64_t seed_index = 0; seed_index < sizeof(seeds) / sizeof(seeds[0]); seed_index++) {
            for (uint64_t len = 0; len < 66; len++) {
                uint32_t sum = ref_checksum_add(seeds[seed_index], raw, len);
                uint64_t observed = ((uint64_t)sum << 16) |
                    ref_checksum_finish(sum);
                digest_add(&digest, observed);
            }
        }
    }
    digest_emit("checksum-grid", &digest);
    total_cases += digest.count;

    digest_reset(&digest);
    for (uint64_t index = 0; index < 65536; index++) {
        uint32_t sum = ((uint32_t)index << 16) |
            (uint32_t)((~index) & 0xffff);
        digest_add(&digest, ref_checksum_finish(sum));
    }
    digest_emit("checksum-finish-grid", &digest);
    total_cases += digest.count;

    static const int64_t classes[] = {1, 2, 3};
    static const int64_t subclasses[] = {-1, 0, 1};
    static const int64_t vendors[] = {0x1af3, 0x1af4, 0x1af5};
    static const int64_t devices[] = {
        0x0fff, 0x1000, 0x1001, 0x100f, 0x1010, 0x1011, 0x1012,
        0x1013, 0x1040, 0x1041, 0x1042, 0x1043, 0x104f, 0x1050,
        0x1051, 0x1052, 0x1053
    };
    digest_reset(&digest);
    for (uint64_t class_index = 0; class_index < sizeof(classes) / sizeof(classes[0]); class_index++) {
        for (uint64_t subclass_index = 0; subclass_index < sizeof(subclasses) / sizeof(subclasses[0]); subclass_index++) {
            for (uint64_t vendor_index = 0; vendor_index < sizeof(vendors) / sizeof(vendors[0]); vendor_index++) {
                for (uint64_t device_index = 0; device_index < sizeof(devices) / sizeof(devices[0]); device_index++) {
                    uint64_t net = (uint64_t)ref_virtio_net(
                        classes[class_index], subclasses[subclass_index],
                        vendors[vendor_index], devices[device_index]);
                    uint64_t gpu = (uint64_t)ref_virtio_gpu(
                        classes[class_index], subclasses[subclass_index],
                        vendors[vendor_index], devices[device_index]);
                    digest_add(&digest, net | (gpu << 1));
                }
            }
        }
    }
    digest_emit("virtio-net-gpu-grid", &digest);
    total_cases += digest.count;

    digest_reset(&digest);
    for (uint64_t vendor_index = 0; vendor_index < sizeof(vendors) / sizeof(vendors[0]); vendor_index++) {
        for (uint64_t device_index = 0; device_index < sizeof(devices) / sizeof(devices[0]); device_index++) {
            uint64_t blk = (uint64_t)ref_virtio_blk(
                vendors[vendor_index], devices[device_index]);
            uint64_t input = (uint64_t)ref_virtio_input(
                vendors[vendor_index], devices[device_index]);
            digest_add(&digest, blk | (input << 1));
        }
    }
    digest_emit("virtio-blk-input-grid", &digest);
    total_cases += digest.count;

    printf("rv64-freestanding-policy oracle_cases=%llu decision_outcomes=34\n",
           (unsigned long long)total_cases);
    return 0;
}
