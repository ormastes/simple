#include <stdint.h>
#include <stdio.h>

uint16_t rt_be16(const uint8_t *p);
uint32_t rt_be32(const uint8_t *p);
void rt_put_be16(uint8_t *p, uint16_t value);
void rt_put_be32(uint8_t *p, uint32_t value);
uint32_t rt_checksum_add(uint32_t sum, const uint8_t *data, uint64_t len);
uint16_t rt_checksum_finish(uint32_t sum);
int64_t rt_pci_is_virtio_net(int64_t cls, int64_t sub, int64_t vendor,
                             int64_t device_id);
int64_t rt_pci_is_virtio_gpu(int64_t cls, int64_t sub, int64_t vendor,
                             int64_t device_id);
int64_t rt_pci_is_virtio_blk(int64_t vendor, int64_t device_id);
int64_t rt_pci_is_virtio_input(int64_t vendor, int64_t device_id);
void rt_put_le32(uint8_t *p, uint32_t value);
void rt_put_le64(uint8_t *p, uint64_t value);
uint32_t rt_get_le32(const uint8_t *p);

static uint64_t bridge_reads;
static uint64_t bridge_writes;

uint64_t rt_volatile_read_u8(uint64_t addr) {
    bridge_reads++;
    return *(const volatile uint8_t *)(uintptr_t)addr;
}

void rt_volatile_write_u8(uint64_t addr, uint64_t value) {
    bridge_writes++;
    *(volatile uint8_t *)(uintptr_t)addr = (uint8_t)value;
}

static int check(int condition, const char *name) {
    if (!condition) {
        fprintf(stderr, "rv64_freestanding_policy_c_abi status=FAIL check=%s\n", name);
        return 0;
    }
    return 1;
}

int main(void) {
    uint8_t buffer[16] = {0x12, 0x34, 0x56, 0x78, 0x9a};
    int ok = 1;

    ok &= check(rt_be16(buffer) == UINT16_C(0x1234), "be16");
    ok &= check(rt_be32(buffer) == UINT32_C(0x12345678), "be32");
    ok &= check(rt_checksum_add(0, buffer, 5) == UINT32_C(0x102ac),
                "checksum-add");
    ok &= check(rt_checksum_finish(UINT32_C(0x102ac)) == UINT16_C(0xfd52),
                "checksum-finish");

    rt_put_be16(buffer, UINT16_C(0xabcd));
    ok &= check(buffer[0] == 0xab && buffer[1] == 0xcd, "put-be16");
    rt_put_be32(buffer, UINT32_C(0x89abcdef));
    ok &= check(buffer[0] == 0x89 && buffer[1] == 0xab &&
                buffer[2] == 0xcd && buffer[3] == 0xef, "put-be32");

    ok &= check(rt_pci_is_virtio_net(2, 0, 0x1af4, 0x1000) == 1,
                "virtio-net-legacy");
    ok &= check(rt_pci_is_virtio_net(2, 1, 0x1af4, 0x1041) == 0,
                "virtio-net-class");
    ok &= check(rt_pci_is_virtio_gpu(0xff, -1, 0x1af4, 0x1050) == 1,
                "virtio-gpu-modern-class-ignored");
    ok &= check(rt_pci_is_virtio_blk(0x1af4, 0x1042) == 1,
                "virtio-blk-modern");
    ok &= check(rt_pci_is_virtio_input(0x1af4, 0x1052) == 1,
                "virtio-input-modern");
    ok &= check(rt_pci_is_virtio_input(0x1af5, 0x1052) == 0,
                "virtio-input-vendor");

    rt_put_le32(buffer, UINT32_C(0x76543210));
    ok &= check(buffer[0] == 0x10 && buffer[1] == 0x32 &&
                buffer[2] == 0x54 && buffer[3] == 0x76, "put-le32");
    ok &= check(rt_get_le32(buffer) == UINT32_C(0x76543210), "get-le32");
    rt_put_le64(buffer, UINT64_C(0x0123456789abcdef));
    ok &= check(buffer[0] == 0xef && buffer[1] == 0xcd &&
                buffer[2] == 0xab && buffer[3] == 0x89 &&
                buffer[4] == 0x67 && buffer[5] == 0x45 &&
                buffer[6] == 0x23 && buffer[7] == 0x01, "put-le64");

    ok &= check(bridge_reads == 15, "bridge-read-count");
    ok &= check(bridge_writes == 18, "bridge-write-count");
    if (!ok) return 1;

    printf("rv64_freestanding_policy_c_abi status=PASS exports=13/13 bridge_reads=%llu bridge_writes=%llu\n",
           (unsigned long long)bridge_reads,
           (unsigned long long)bridge_writes);
    return 0;
}
