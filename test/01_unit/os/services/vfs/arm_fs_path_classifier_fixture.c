#include <assert.h>
#include <string.h>
#include <stdint.h>
#include "../../../../../examples/09_embedded/simple_os/arch/arm64/boot/arm_fs_path_classifier.h"
#include "../../../../../examples/09_embedded/simple_os/arch/arm64/boot/arm_fs_root_dirent.h"
#include "../../../../../examples/09_embedded/simple_os/arch/arm64/boot/arm64_user_map_contract.h"
#include "../../../../../examples/09_embedded/simple_os/arch/arm64/boot/arm64_elf_preflight_contract.h"

static uint32_t classify(const char *text) { return arm_fs_classify_path_bytes(text, strlen(text)); }

int main(void)
{
    /* Exact mounted HELLO ELF header/LOAD facts: len=145, phoff=64, one LOAD,
       fileoff=0, VA=0x1000, filesz=memsz=145. */
    uint8_t hello[145]={0x7f,'E','L','F',2,1,1}; hello[16]=2;hello[18]=183;hello[20]=1;
    hello[24]=0x00;hello[25]=0x10;hello[32]=64;hello[52]=64;hello[54]=56;hello[56]=1;
    hello[64]=1;hello[68]=5;hello[80]=0x00;hello[81]=0x10;hello[96]=145;hello[104]=145;
    assert(arm64_elf_preflight_bytes(hello,sizeof hello)==ARM64_ELF_OK);
    hello[104]=144;assert(arm64_elf_preflight_bytes(hello,sizeof hello)==ARM64_ELF_FILE_GT_MEM);hello[104]=145;
    hello[96]=146;hello[104]=146;assert(arm64_elf_preflight_bytes(hello,sizeof hello)==ARM64_ELF_SOURCE_BOUNDS);
    hello[96]=145;hello[104]=145;hello[18]=62;assert(arm64_elf_preflight_bytes(hello,sizeof hello)==ARM64_ELF_MACHINE);hello[18]=183;
    assert(arm64_user_map_precondition_reason(1, 0x48000000, 0x200000, 0x48100000) == ARM64_USER_MAP_OK);
    assert(arm64_user_map_precondition_reason(0, 0x48000000, 0x200000, 0x48100000) == ARM64_USER_MAP_UNKNOWN_ROOT);
    assert(arm64_user_map_precondition_reason(1, 0, 0x200000, 0x48100000) == ARM64_USER_MAP_ZERO_ROOT);
    assert(arm64_user_map_precondition_reason(1, 0x48000000, 0x200001, 0x48100000) == ARM64_USER_MAP_VA_UNALIGNED);
    assert(arm64_user_map_precondition_reason(1, 0x48000000, 0x200000, 0x48100001) == ARM64_USER_MAP_PA_UNALIGNED);
    /* Exact live10 FAT root dirent: cluster 247, fixed nonce slot size 118. */
    uint8_t nonce_dirent[32] = {
        'Q','E','M','U','N','O','N','C','T','X','T',0x20,
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0xf7,0,0x76,0,0,0
    };
    struct arm_fs_root_dirent_metadata_v1 metadata;
    assert(arm_fs_root_dirent_metadata(nonce_dirent, sizeof(nonce_dirent), 1, &metadata));
    assert(metadata.first_cluster == 247 && metadata.size == 118);
    nonce_dirent[7] = 'X';
    assert(!arm_fs_root_dirent_metadata(nonce_dirent, sizeof(nonce_dirent), 1, &metadata));
    nonce_dirent[7] = 'C';
    assert(!arm_fs_root_dirent_metadata(nonce_dirent, 31, 1, &metadata));
    assert(!arm_fs_root_dirent_metadata(nonce_dirent, sizeof(nonce_dirent), 0, &metadata));
    assert(classify("/QEMUNONC.TXT") == ARM_FS_ROUTE_ROOT_QEMU_NONCE);
    assert(classify("/FSEXEC.ELF") == ARM_FS_ROUTE_ROOT_FS_EXEC);
    assert(classify("/SIMPLE.ELF") == ARM_FS_ROUTE_ROOT_SIMPLE);
    assert(classify("/HELLO.SPL") == ARM_FS_ROUTE_ROOT_HELLO_SPL);
    assert(classify("/SYS/APPS/HELLOSMF.SMF") == ARM_FS_ROUTE_SYS_APPS);
    assert(classify("/SYS/VERSION.TXT") == ARM_FS_ROUTE_SYS);
    assert(classify("/qemunonc.txt") == ARM_FS_ROUTE_REJECT);
    assert(classify("/QEMUNONC.TXT ") == ARM_FS_ROUTE_REJECT);
    assert(classify("/QEMUNONC.TX") == ARM_FS_ROUTE_REJECT);
    assert(classify("/SYS/APPS/") == ARM_FS_ROUTE_REJECT);
    assert(classify("/SYS/APPSX/HELLO") == ARM_FS_ROUTE_SYS);
    assert(arm_fs_classify_path_bytes("/QEMUNONC.TXT\0X", 16) == ARM_FS_ROUTE_REJECT);
    assert(classify("/UNKNOWN.ROOT") == ARM_FS_ROUTE_REJECT);

    union {
        uint64_t align;
        unsigned char bytes[256];
    } heap;
    memset(&heap, 0, sizeof(heap));
    struct arm_fs_runtime_string_v1 *runtime = (struct arm_fs_runtime_string_v1 *)heap.bytes;
    const char *path = "/QEMUNONC.TXT";
    runtime->type = 1;
    runtime->len = strlen(path);
    runtime->size = (uint32_t)(sizeof(*runtime) + runtime->len + 1);
    memcpy(runtime->data, path, runtime->len + 1);
    uintptr_t base = (uintptr_t)heap.bytes;
    uintptr_t end = base + sizeof(heap.bytes);
    struct arm_fs_runtime_string_receipt_v1 receipt;
    assert(arm_fs_classify_runtime_string_receipt(base | 1ULL, base, end, 1, &receipt) == ARM_FS_ROUTE_ROOT_QEMU_NONCE);
    assert(receipt.reason == ARM_FS_TEXT_ACCEPTED && receipt.tag == 1 && receipt.candidate == base);
    assert(arm_fs_classify_runtime_string(base, base, end, 1) == ARM_FS_ROUTE_ROOT_QEMU_NONCE);
    assert(arm_fs_classify_runtime_string(base | 1ULL, base, end, 1) == ARM_FS_ROUTE_ROOT_QEMU_NONCE);
    assert(arm_fs_classify_runtime_string(base - 8, base, end, 1) == ARM_FS_ROUTE_REJECT);
    assert(arm_fs_classify_runtime_string(end + 8, base, end, 1) == ARM_FS_ROUTE_REJECT);
    runtime->type = 2;
    assert(arm_fs_classify_runtime_string(base, base, end, 1) == ARM_FS_ROUTE_REJECT);
    arm_fs_classify_runtime_string_receipt(base, base, end, 1, &receipt);
    assert(receipt.reason == ARM_FS_TEXT_WRONG_TYPE && receipt.type == 2);
    runtime->type = 1;
    runtime->len = 4097;
    assert(arm_fs_classify_runtime_string(base, base, end, 1) == ARM_FS_ROUTE_REJECT);
    arm_fs_classify_runtime_string_receipt(base, base, end, 1, &receipt);
    assert(receipt.reason == ARM_FS_TEXT_LENGTH_LIMIT && receipt.len == 4097);
    runtime->len = strlen(path);
    runtime->size = (uint32_t)(sizeof(*runtime) + runtime->len);
    assert(arm_fs_classify_runtime_string(base, base, end, 1) == ARM_FS_ROUTE_REJECT);
    runtime->size++;
    runtime->data[runtime->len] = 'X';
    assert(arm_fs_classify_runtime_string(base, base, end, 1) == ARM_FS_ROUTE_REJECT);
    runtime->data[runtime->len] = '\0';
    runtime->data[4] = '\0';
    assert(arm_fs_classify_runtime_string(base, base, end, 1) == ARM_FS_ROUTE_REJECT);
    return 0;
}
