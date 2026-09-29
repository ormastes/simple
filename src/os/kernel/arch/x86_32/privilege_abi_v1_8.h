#ifndef SIMPLEOS_X86_32_PRIVILEGE_ABI_V1_8_H
#define SIMPLEOS_X86_32_PRIVILEGE_ABI_V1_8_H

/* Raw freestanding i686 ABI. Do not include hosted headers here. */
typedef unsigned char simpleos_x32_u8;
typedef unsigned int simpleos_x32_u32;
typedef signed int simpleos_x32_i32;
typedef unsigned long long simpleos_x32_u64;

#define SIMPLEOS_X32_PRIV_ABI_VERSION 0x00010008U
#define SIMPLEOS_X32_BOOT_PAGING_POOL_PAGES 3U
#define SIMPLEOS_X32_BOOT_PAGING_POOL_BYTES 12288U
#define SIMPLEOS_X32_PRIV_DISPATCH_SYMBOL simpleos_x86_32_privilege_dispatch_v1_1
#define SIMPLEOS_X32_PRIV_ENTER_SYMBOL simpleos_x86_32_privilege_enter_v1_2
#define SIMPLEOS_X32_PRIV_CLEAR_SYMBOL simpleos_x86_32_privilege_clear_active_v1_2
#define SIMPLEOS_X32_KERNEL_STACK_PAGES 4U
#define SIMPLEOS_X32_KERNEL_STACK_BYTES 16384U
#define SIMPLEOS_X32_NONCE_USER_VA 0x2FFFF000U
#define SIMPLEOS_X32_NONCE_PAGE_BYTES 4096U
#define SIMPLEOS_X32_TOKEN_REGISTRY_SLOTS 16U
#define SIMPLEOS_X32_RECURSIVE_PDE_INDEX 1023U
#define SIMPLEOS_X32_RECURSIVE_PT_BASE 0xFFC00000U
#define SIMPLEOS_X32_RECURSIVE_PD_VA 0xFFFFF000U
#define SIMPLEOS_X32_KMAP_VA 0xFFBFF000U

typedef struct __attribute__((packed)) {
    simpleos_x32_u32 gs, fs, es, ds;
    simpleos_x32_u32 edi, esi, ebp, esp_dummy;
    simpleos_x32_u32 ebx, edx, ecx, eax;
    simpleos_x32_u32 vector, error;
    simpleos_x32_u32 eip, cs, eflags, user_esp, user_ss;
} SimpleOsX86_32TrapFrameV1;

typedef struct __attribute__((packed)) {
    simpleos_x32_u32 magic, version, state, reserved0;
    simpleos_x32_u64 task_id, task_generation, address_space_id;
    simpleos_x32_u32 expected_cr3, kernel_cr3, kernel_esp, kernel_resume_eip;
    simpleos_x32_u32 expected_nonce_user_va;
    simpleos_x32_u32 nonce_length;
    simpleos_x32_u8 nonce_digest[32];
} SimpleOsX86_32PrivilegeTokenV1;

typedef struct __attribute__((packed)) {
    simpleos_x32_u32 action;
    simpleos_x32_i32 eax;
    simpleos_x32_u32 kernel_esp, kernel_eip;
} SimpleOsX86_32TrapDispositionV1;

#define SIMPLEOS_X32_OFFSETOF(type, field) ((simpleos_x32_u32)__builtin_offsetof(type, field))
_Static_assert(sizeof(simpleos_x32_u32) == 4, "i686 u32 required");
_Static_assert(sizeof(simpleos_x32_u64) == 8, "i686 u64 required");
_Static_assert(sizeof(SimpleOsX86_32TrapFrameV1) == 76, "trap frame ABI drift");
_Static_assert(SIMPLEOS_X32_OFFSETOF(SimpleOsX86_32TrapFrameV1, eip) == 56, "eip offset drift");
_Static_assert(SIMPLEOS_X32_OFFSETOF(SimpleOsX86_32TrapFrameV1, user_ss) == 72, "user ss offset drift");
_Static_assert(sizeof(SimpleOsX86_32PrivilegeTokenV1) == 96, "token ABI drift");
_Static_assert(SIMPLEOS_X32_OFFSETOF(SimpleOsX86_32PrivilegeTokenV1, task_id) == 16, "task offset drift");
_Static_assert(SIMPLEOS_X32_OFFSETOF(SimpleOsX86_32PrivilegeTokenV1, expected_cr3) == 40, "cr3 offset drift");
_Static_assert(SIMPLEOS_X32_OFFSETOF(SimpleOsX86_32PrivilegeTokenV1, expected_nonce_user_va) == 56, "nonce VA drift");
_Static_assert(SIMPLEOS_X32_OFFSETOF(SimpleOsX86_32PrivilegeTokenV1, nonce_length) == 60, "nonce length drift");
_Static_assert(SIMPLEOS_X32_OFFSETOF(SimpleOsX86_32PrivilegeTokenV1, nonce_digest) == 64, "nonce digest drift");
_Static_assert(sizeof(SimpleOsX86_32TrapDispositionV1) == 16, "disposition ABI drift");

/*
 * cdecl, strong and unique. Arguments are four 32-bit stack words in order.
 * frame/token/out must be non-null and 4-byte aligned. observed_cr3 is the
 * caller's direct CR3 observation. Return 0 only with all 16 out bytes set;
 * negative errno rejects and the caller must ignore out entirely.
 */
simpleos_x32_i32 SIMPLEOS_X32_PRIV_DISPATCH_SYMBOL(
    const SimpleOsX86_32TrapFrameV1 *frame,
    SimpleOsX86_32PrivilegeTokenV1 *token,
    simpleos_x32_u32 observed_cr3,
    SimpleOsX86_32TrapDispositionV1 *disposition_out
) __attribute__((cdecl, visibility("hidden")));

/*
 * Strong cdecl first-entry ABI. token is non-null/4-aligned; kernel_stack_top
 * is nonzero/16-aligned; eip/user_esp are nonzero; user_cr3 is page aligned.
 * The owner rejects an occupied CPU-local active slot, writes TSS.esp0 first,
 * release-publishes token second, switches CR3, loads ECX from
 * token.expected_nonce_user_va and EDX from token.nonce_length, then irets.
 * The nonce range is mapped user-readable, kernel-read-only, exact length,
 * at most 4096 bytes, below 0xC0000000, and checked without wrapping.
 */
void SIMPLEOS_X32_PRIV_ENTER_SYMBOL(
    SimpleOsX86_32PrivilegeTokenV1 *token,
    simpleos_x32_u32 kernel_stack_top,
    simpleos_x32_u32 eip,
    simpleos_x32_u32 user_esp,
    simpleos_x32_u32 user_cr3
) __attribute__((cdecl, noreturn, visibility("hidden")));

/* Compare-and-clear the exact active token once. 0=cleared, -13=mismatch. */
simpleos_x32_i32 SIMPLEOS_X32_PRIV_CLEAR_SYMBOL(
    SimpleOsX86_32PrivilegeTokenV1 *expected_token
) __attribute__((cdecl, visibility("hidden")));

/* Syscall 60 accepts only EBX==expected_nonce_user_va and ECX==nonce_length;
 * it overflow-checks EBX+ECX, revalidates every mapped read-only page under
 * expected_cr3, hashes exactly ECX bytes, and compares all 32 digest bytes
 * before emitting any output. */

#endif
