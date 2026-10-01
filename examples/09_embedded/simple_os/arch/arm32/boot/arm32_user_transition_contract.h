#ifndef SIMPLEOS_ARM32_USER_TRANSITION_CONTRACT_H
#define SIMPLEOS_ARM32_USER_TRANSITION_CONTRACT_H

#include <stddef.h>
#include <stdint.h>

#define ARM32_USER_ABI_VERSION 0x00010006u
#define ARM32_CPSR_USR 0x10u
#define ARM32_CPSR_MODE_MASK 0x1fu
#define ARM32_HANDOFF_TOKEN_MAGIC 0x41333255u
#define ARM32_SVC_EXIT 0u
#define ARM32_SVC_WRITE_STDOUT 60u
#define ARM32_EXPECTED_EXIT 37u
#define ARM32_TOKEN_PREPARED 1u
#define ARM32_TOKEN_RUNNING 2u
#define ARM32_TOKEN_EXITED 3u
#define ARM32_TOKEN_REAPED 4u
#define ARM32_TOKEN_MAC_KEY_BYTES 16u
#define ARM32_TOKEN_MAC_INPUT_BYTES 72u
#define ARM32_SVC_STACK_BYTES 4096u
#define ARM32_SVC_FRAME_BYTES 72u
#define ARM32_TOKEN_MAC_DOMAIN "SOSIX-A32-TOK1.1"
#define ARM32_MAX_CPU_SLOTS 4u
#define ARM32_VECTOR_SECTION ".vectors.arm32.v12"
#define ARM32_VECTOR_SYMBOL arm32_vector_table_v12

enum Arm32UserMapFlagsV12 {
    ARM32_MAP_USER = 1u,
    ARM32_MAP_WRITE = 2u,
    ARM32_MAP_EXEC = 4u,
    ARM32_MAP_DEVICE = 8u,
    ARM32_MAP_SHARED = 16u,
    ARM32_MAP_FLAGS_MASK = 31u
};

/* ARMv7 short-descriptor small-page bit positions. */
#define ARM32_L2_XN (1u << 0)
#define ARM32_L2_SMALL_PAGE (1u << 1)
#define ARM32_L2_B (1u << 2)
#define ARM32_L2_C (1u << 3)
#define ARM32_L2_AP_RW_ALL (3u << 4)       /* AP=011 */
#define ARM32_L2_AP_RO_ALL ((2u << 4) | (1u << 9)) /* AP=110 */
#define ARM32_L2_TEX_NORMAL_WBWA (1u << 6)
#define ARM32_L2_S (1u << 10)
#define ARM32_L2_NG (1u << 11)
#define ARM32_L2_BASE_MASK 0xfffff000u
#define ARM32_L1_COARSE_PAGE_TABLE 1u
#define ARM32_L1_COARSE_BASE_MASK 0xfffffc00u
#define ARM32_L1_DOMAIN 0u
#define ARM32_DACR_DOMAIN0_CLIENT 1u
#define ARM32_USER_TABLE_ARENA_BYTES (1024u * 1024u)
#define ARM32_USER_TABLE_PAGE_BYTES 4096u
#define ARM32_USER_TABLE_PAGE_COUNT 256u
#define ARM32_USER_L1_PAGES 4u
#define ARM32_USER_FRAME_ARENA_BYTES (4u * 1024u * 1024u)
#define ARM32_USER_FRAME_PAGE_COUNT 1024u

static inline int arm32_user_map_flags_valid_v12(uint32_t flags)
{
    if ((flags & ~ARM32_MAP_FLAGS_MASK) != 0 ||
        (flags & ARM32_MAP_USER) == 0) return 0;
    if ((flags & ARM32_MAP_WRITE) && (flags & ARM32_MAP_EXEC)) return 0;
    if ((flags & ARM32_MAP_DEVICE) &&
        ((flags & ARM32_MAP_EXEC) || !(flags & ARM32_MAP_SHARED))) return 0;
    return 1;
}

static inline uint32_t arm32_user_l2_attrs_v12(uint32_t flags)
{
    uint32_t attrs;
    if (!arm32_user_map_flags_valid_v12(flags)) return 0;
    attrs = ARM32_L2_SMALL_PAGE | ARM32_L2_NG;
    attrs |= (flags & ARM32_MAP_WRITE) ? ARM32_L2_AP_RW_ALL : ARM32_L2_AP_RO_ALL;
    if (!(flags & ARM32_MAP_EXEC)) attrs |= ARM32_L2_XN;
    if (flags & ARM32_MAP_DEVICE) attrs |= ARM32_L2_B | ARM32_L2_S;
    else attrs |= ARM32_L2_TEX_NORMAL_WBWA | ARM32_L2_C | ARM32_L2_B;
    if (flags & ARM32_MAP_SHARED) attrs |= ARM32_L2_S;
    return attrs;
}

static inline int arm32_cpu_slot_valid_v12(uint32_t mpidr_aff0)
{
    return mpidr_aff0 < ARM32_MAX_CPU_SLOTS;
}

static inline int arm32_vbar_valid_v12(
    uint32_t vector, uint32_t kernel_start, uint32_t kernel_end)
{
    return (vector & 31u) == 0 && vector >= kernel_start &&
        vector <= kernel_end - 32u;
}

static inline int arm32_boot_secret_valid_v12(
    const uint8_t secret[ARM32_TOKEN_MAC_KEY_BYTES])
{
    uint8_t any = 0;
    unsigned i;
    for (i = 0; i < ARM32_TOKEN_MAC_KEY_BYTES; ++i) any |= secret[i];
    return any != 0;
}

static inline void arm32_boot_secret_wipe_v12(
    uint8_t secret[ARM32_TOKEN_MAC_KEY_BYTES])
{
    volatile uint8_t *p = secret;
    unsigned i;
    for (i = 0; i < ARM32_TOKEN_MAC_KEY_BYTES; ++i) p[i] = 0;
}

typedef struct Arm32SvcFrameV1 {
    uint32_t r[13];
    uint32_t user_sp;
    uint32_t user_lr;
    uint32_t return_pc;
    uint32_t spsr;
    uint32_t svc_instruction;
} Arm32SvcFrameV1;

typedef struct Arm32UserHandoffTokenV1 {
    uint32_t magic, version, task_id, task_generation;
    uint32_t address_space_id, user_ttbr0_root, nonce_lo, nonce_hi;
    uint32_t supervisor_sp, supervisor_pc, kernel_ttbr0_root, lifecycle_state;
    uint32_t auth_tag_lo, auth_tag_hi, expected_frame_sp, syscall_sequence;
} Arm32UserHandoffTokenV1;

enum Arm32SvcActionV1 {
    ARM32_SVC_ACTION_REJECT = 0,
    ARM32_SVC_ACTION_RETURN_USER = 1,
    ARM32_SVC_ACTION_RESUME_SUPERVISOR = 2
};

enum Arm32DispositionActionV14 {
    ARM32_DISPOSITION_REJECT = 0,
    ARM32_DISPOSITION_STDOUT_BYTE = 1,
    ARM32_DISPOSITION_EXIT = 2,
    ARM32_DISPOSITION_FAULT = 3
};
enum Arm32DispositionStatusV14 {
    ARM32_DISPOSITION_OK = 0,
    ARM32_DISPOSITION_BAD_AUTH = 1,
    ARM32_DISPOSITION_BAD_SYSCALL = 2,
    ARM32_DISPOSITION_BAD_PAYLOAD = 3,
    ARM32_DISPOSITION_REPLAY = 4
};
typedef struct Arm32SvcDispositionV14 {
    uint32_t action, status, stdout_byte, exit_code;
    uint32_t fault_code, task_id, task_generation, syscall_sequence;
    uint32_t auth_receipt_lo, auth_receipt_hi, observed_ttbr0, frame_sp;
    uint32_t return_pc, spsr, reserved0, reserved1;
} Arm32SvcDispositionV14;
_Static_assert(sizeof(Arm32SvcDispositionV14) == 64, "disposition size");
_Static_assert(offsetof(Arm32SvcDispositionV14, task_id) == 20, "disposition task offset");
_Static_assert(offsetof(Arm32SvcDispositionV14, auth_receipt_lo) == 32, "receipt offset");

_Static_assert(sizeof(Arm32SvcFrameV1) == 72, "ARM32 SVC frame size");
_Static_assert(offsetof(Arm32SvcFrameV1, user_sp) == 52, "user SP offset");
_Static_assert(offsetof(Arm32SvcFrameV1, return_pc) == 60, "return PC offset");
_Static_assert(offsetof(Arm32SvcFrameV1, spsr) == 64, "SPSR offset");
_Static_assert(offsetof(Arm32SvcFrameV1, svc_instruction) == 68, "SVC offset");
_Static_assert(sizeof(Arm32UserHandoffTokenV1) == 64, "handoff token size");
_Static_assert(offsetof(Arm32UserHandoffTokenV1, user_ttbr0_root) == 20, "TTBR0 offset");
_Static_assert(offsetof(Arm32UserHandoffTokenV1, supervisor_sp) == 32, "SVC SP offset");
_Static_assert(offsetof(Arm32UserHandoffTokenV1, auth_tag_lo) == 48, "auth offset");
_Static_assert(sizeof(ARM32_TOKEN_MAC_DOMAIN) - 1 == 16, "MAC domain size");

/*
 * v1.1 MAC = SipHash-2-4 with the scheduler's 128-bit boot key.
 * Input is exactly 72 bytes: the 16 domain bytes above, then little-endian
 * token words 0..11 and 14..15.  auth_tag_lo/hi (words 12..13) are excluded.
 * The 64-bit SipHash result is stored low word then high word and verified by
 * XOR/OR accumulation without data-dependent early return.
 */
static inline void arm32_token_mac_input_v11(
    uint8_t out[ARM32_TOKEN_MAC_INPUT_BYTES],
    const Arm32UserHandoffTokenV1 *token)
{
    static const uint8_t domain[] = ARM32_TOKEN_MAC_DOMAIN;
    const uint32_t *words = (const uint32_t *)(const void *)token;
    uint32_t selected[14];
    unsigned i, j;
    for (i = 0; i < 16; ++i) out[i] = domain[i];
    for (i = 0; i < 12; ++i) selected[i] = words[i];
    selected[12] = words[14];
    selected[13] = words[15];
    for (i = 0; i < 14; ++i)
        for (j = 0; j < 4; ++j)
            out[16 + i * 4 + j] = (uint8_t)(selected[i] >> (j * 8));
}

static inline uint32_t arm32_expected_svc_frame_sp(uint32_t svc_stack_top)
{
    return svc_stack_top - ARM32_SVC_FRAME_BYTES;
}

/* Future assembly/C owners must implement exactly these ports. */
void arm32_vector_install_v1(uint32_t vector_phys);
int arm32_user_l1_create_v1(uint32_t address_space_id, uint32_t *root_out);
int arm32_user_l1_map_v1(uint32_t root, uint32_t va, uint32_t pa, uint32_t flags);
int arm32_user_l1_destroy_v1(uint32_t root, uint32_t address_space_id);
int arm32_enter_user_v1(Arm32UserHandoffTokenV1 *token, uint32_t entry, uint32_t user_sp);
enum Arm32SvcActionV1 arm32_svc_dispatch_v1(
    Arm32SvcFrameV1 *frame, Arm32UserHandoffTokenV1 *token,
    uint32_t observed_ttbr0);
int arm32_svc_dispatch_disposition_v14(
    uint32_t cpu_id, const Arm32SvcFrameV1 *frame, uint32_t observed_ttbr0,
    Arm32SvcDispositionV14 *out);
enum Arm32SvcActionV1 arm32_scheduler_commit_disposition_v14(
    uint32_t cpu_id, const Arm32SvcDispositionV14 *disposition);
#define ARM32_STDOUT_CAPTURE_BYTES 256u
uint32_t arm32_scheduler_stdout_len_v14(uint32_t cpu_id);
int arm32_scheduler_stdout_copy_v14(uint32_t cpu_id, uint8_t *out,
                                    uint32_t capacity);
int arm32_scheduler_reap_v14(uint32_t cpu_id, uint32_t task_id,
                             uint32_t task_generation);

/* Scheduler-owned registry. Exactly 16 nonzero entropy bytes are copied into
 * privileged-only storage and volatile-wiped from the caller on every path.
 * A repeated bootstrap fails; no secret or active-token slot is user mapped. */
int arm32_token_registry_bootstrap_v11(
    uint32_t cpu_count, uint8_t boot_secret[ARM32_TOKEN_MAC_KEY_BYTES]);
int arm32_token_issue_v11(
    uint32_t cpu_id, Arm32UserHandoffTokenV1 *token,
    uint32_t task_id, uint32_t task_generation, uint32_t address_space_id,
    uint32_t user_ttbr0_root, uint64_t nonce, uint32_t svc_stack_top,
    uint32_t supervisor_pc, uint32_t kernel_ttbr0_root);
Arm32UserHandoffTokenV1 *arm32_token_lookup_active_v11(uint32_t cpu_id);
int arm32_token_authenticate_v11(
    uint32_t cpu_id, const Arm32SvcFrameV1 *frame, uint32_t observed_ttbr0);
int arm32_token_advance_v11(
    uint32_t cpu_id, uint32_t expected_state, uint32_t next_state);
int arm32_token_revoke_v11(
    uint32_t cpu_id, uint32_t task_id, uint32_t task_generation);

/* Platform ownership: MPIDR.Aff0 is the slot; values >= 4 are rejected. */
uint32_t arm32_platform_cpu_id_v12(void);
extern const uint32_t arm32_vector_table_v12[];

/* v1.3 owner ports. The arena is kernel-only and identity mapped: its kernel
 * address equals the physical descriptor address. */
int arm32_user_table_arena_init_v13(uint32_t kernel_identity_start,
                                    uint32_t kernel_identity_end);
uint32_t arm32_user_table_alloc_l1_v13(uint32_t address_space_id);
uint32_t arm32_user_table_alloc_l2_v13(uint32_t address_space_id,
                                      uint32_t l1_index);
int arm32_user_table_free_space_v13(uint32_t address_space_id,
                                   uint32_t root);
uint32_t arm32_user_table_arena_start_v13(void);
uint32_t arm32_user_table_arena_end_v13(void);
uint64_t arm32_token_siphash24_v13(const uint8_t key[16],
                                  const uint8_t msg[72]);
int arm32_token_siphash24_kat_v13(void);
int arm32_kernel_guard_page_install_v15(uint32_t kernel_root,
                                        uint32_t guard_va, uint32_t cpu_id);
int arm32_kernel_guard_page_restore_v15(uint32_t kernel_root,
                                        uint32_t guard_va, uint32_t cpu_id);
typedef struct Arm32StagedImageV15 {
    uint32_t entry, user_sp, user_root, address_space_id;
    uint32_t svc_stack_top, svc_guard_va, mapped_pages, reserved;
} Arm32StagedImageV15;
_Static_assert(sizeof(Arm32StagedImageV15)==32,"staged image size");
int arm32_user_frame_arena_init_v15(uint32_t identity_start,
                                    uint32_t identity_end);
int arm32_stage_elf32_v15(uint32_t address_space_id, uint32_t kernel_root,
                          uint32_t cpu_id, const uint8_t *elf,
                          uint32_t elf_len, Arm32StagedImageV15 *out);
int arm32_user_frames_free_v15(uint32_t address_space_id);
uint32_t arm32_qemu_nonce_read_v15(uint8_t out[96]);
/* Sole mounted `/FSEXEC.ELF` loan. The exact pointer/length must be returned;
 * release volatile-wipes the fixed kernel-only buffer before reuse. */
int arm32_fsexec_loan_v16(const uint8_t **bytes_out, uint32_t *len_out);
int arm32_fsexec_release_v16(const uint8_t *expected_bytes,
                             uint32_t expected_len);
uint32_t arm32_kernel_ttbr0_root_v16(void);
int arm32_fsexec_resume_prepare_v16(uint32_t task_id,
                                    uint32_t task_generation,
                                    uint32_t kernel_root,
                                    uint32_t svc_guard_va);
uint32_t arm32_fsexec_supervisor_resume_pc_v16(void);
void arm32_fsexec_supervisor_resume_v16(void) __attribute__((noreturn));
int arm32_fsexec_launch_v16(void);

enum Arm32EntropyProvenanceV16 {
    ARM32_ENTROPY_UNAVAILABLE = 0,
    ARM32_ENTROPY_VIRTIO_RNG_MMIO = 1
};
int arm32_virtio_rng_boot_key16_v16(uint8_t key[16], uint32_t *provenance);
int arm32_transition_entropy_bootstrap_v16(uint32_t cpu_count);
static inline int arm32_rng_accumulate_len_v16(uint32_t received,
                                                uint32_t used_len,
                                                uint32_t *next)
{
    if (!next || received >= 16u || used_len == 0u || used_len > 16u-received)
        return 0;
    *next = received + used_len;
    return 1;
}

static inline uint32_t arm32_section_attrs_to_small_v15(uint32_t section)
{
    uint32_t p = ARM32_L2_SMALL_PAGE;
    p |= ((section >> 12) & 7u) << 6; /* TEX */
    p |= section & (ARM32_L2_B | ARM32_L2_C);
    p |= ((section >> 10) & 3u) << 4; /* AP[1:0] */
    p |= ((section >> 15) & 1u) << 9; /* AP[2] */
    p |= ((section >> 16) & 1u) << 10; /* S */
    p |= ((section >> 17) & 1u) << 11; /* nG */
    p |= ((section >> 4) & 1u); /* XN */
    return p;
}

#endif
