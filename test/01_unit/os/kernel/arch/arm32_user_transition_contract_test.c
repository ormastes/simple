#include <assert.h>
#include <stdint.h>
#include <string.h>
#include "../../../../../examples/09_embedded/simple_os/arch/arm32/boot/arm32_user_transition_contract.h"

static int token_shape(const Arm32UserHandoffTokenV1 *t, uint32_t observed_root)
{
    return t && t->magic == ARM32_HANDOFF_TOKEN_MAGIC &&
        t->version == ARM32_USER_ABI_VERSION && t->task_id != 0 &&
        t->task_generation != 0 && t->address_space_id != 0 &&
        t->user_ttbr0_root == observed_root && (observed_root & 0x3fffu) == 0 &&
        t->supervisor_sp != 0 && (t->supervisor_sp & 7u) == 0 &&
        t->supervisor_pc != 0 && t->kernel_ttbr0_root != 0 &&
        (t->auth_tag_lo != 0 || t->auth_tag_hi != 0);
}

int main(void)
{
    Arm32UserHandoffTokenV1 good = {
        ARM32_HANDOFF_TOKEN_MAGIC, ARM32_USER_ABI_VERSION, 7, 3, 9, 0x40400000,
        0x11223344, 0x55667788, 0x407ff000, 0x40201000,
        0x40300000, 1, 0xa5a5a5a5, 0x5a5a5a5a, 0x407fefb8, 0
    };
    assert(token_shape(&good, 0x40400000));
    Arm32UserHandoffTokenV1 forged = good;
    forged.task_generation++;
    forged.auth_tag_lo = forged.auth_tag_hi = 0;
    assert(!token_shape(&forged, 0x40400000));
    assert(!token_shape(&good, 0x40800000));
    forged = good;
    forged.supervisor_sp |= 4;
    assert(!token_shape(&forged, 0x40400000));
    uint8_t base[ARM32_TOKEN_MAC_INPUT_BYTES];
    uint8_t changed[ARM32_TOKEN_MAC_INPUT_BYTES];
    arm32_token_mac_input_v11(base, &good);
    forged = good;
    forged.auth_tag_lo ^= 1; /* stored tag is deliberately not MAC input */
    arm32_token_mac_input_v11(changed, &forged);
    assert(memcmp(base, changed, sizeof base) == 0);
    forged = good;
    forged.task_generation++;
    arm32_token_mac_input_v11(changed, &forged);
    assert(memcmp(base, changed, sizeof base) != 0);
    forged = good;
    forged.nonce_hi ^= 1;
    arm32_token_mac_input_v11(changed, &forged);
    assert(memcmp(base, changed, sizeof base) != 0);
    forged = good;
    forged.expected_frame_sp ^= 8;
    arm32_token_mac_input_v11(changed, &forged);
    assert(memcmp(base, changed, sizeof base) != 0);
    forged = good;
    forged.syscall_sequence++;
    arm32_token_mac_input_v11(changed, &forged);
    assert(memcmp(base, changed, sizeof base) != 0);
    assert(arm32_expected_svc_frame_sp(good.supervisor_sp) == good.expected_frame_sp);
    assert(arm32_user_map_flags_valid_v12(ARM32_MAP_USER | ARM32_MAP_EXEC));
    assert(arm32_user_map_flags_valid_v12(ARM32_MAP_USER | ARM32_MAP_WRITE));
    assert(!arm32_user_map_flags_valid_v12(
        ARM32_MAP_USER | ARM32_MAP_WRITE | ARM32_MAP_EXEC));
    assert(!arm32_user_map_flags_valid_v12(ARM32_MAP_USER | ARM32_MAP_DEVICE));
    assert(!arm32_user_map_flags_valid_v12(ARM32_MAP_USER | 32u));
    uint32_t rx = arm32_user_l2_attrs_v12(ARM32_MAP_USER | ARM32_MAP_EXEC);
    uint32_t rw = arm32_user_l2_attrs_v12(ARM32_MAP_USER | ARM32_MAP_WRITE);
    uint32_t dev = arm32_user_l2_attrs_v12(
        ARM32_MAP_USER | ARM32_MAP_WRITE | ARM32_MAP_DEVICE | ARM32_MAP_SHARED);
    assert((rx & ARM32_L2_XN) == 0 && (rx & ARM32_L2_AP_RO_ALL) == ARM32_L2_AP_RO_ALL);
    assert((rw & ARM32_L2_XN) != 0 && (rw & ARM32_L2_AP_RW_ALL) == ARM32_L2_AP_RW_ALL);
    assert((dev & (ARM32_L2_XN | ARM32_L2_S | ARM32_L2_B)) ==
        (ARM32_L2_XN | ARM32_L2_S | ARM32_L2_B));
    assert((dev & (ARM32_L2_C | ARM32_L2_TEX_NORMAL_WBWA)) == 0);
    uint32_t section = 0x50000000u | 2u | (3u << 10) | (1u << 12) |
        (1u << 3) | (1u << 2) | (1u << 16);
    uint32_t split = arm32_section_attrs_to_small_v15(section);
    assert((split & 3u) == ARM32_L2_SMALL_PAGE);
    assert((split & ARM32_L2_AP_RW_ALL) == ARM32_L2_AP_RW_ALL);
    assert((split & (ARM32_L2_TEX_NORMAL_WBWA | ARM32_L2_C |
        ARM32_L2_B | ARM32_L2_S)) ==
        (ARM32_L2_TEX_NORMAL_WBWA | ARM32_L2_C | ARM32_L2_B | ARM32_L2_S));
    assert(arm32_cpu_slot_valid_v12(3));
    assert(!arm32_cpu_slot_valid_v12(4));
    assert(arm32_vbar_valid_v12(0x40200020, 0x40200000, 0x40300000));
    assert(!arm32_vbar_valid_v12(0x40200024, 0x40200000, 0x40300000));
    uint8_t secret[ARM32_TOKEN_MAC_KEY_BYTES] = {1};
    uint8_t zero_secret[ARM32_TOKEN_MAC_KEY_BYTES] = {0};
    assert(arm32_boot_secret_valid_v12(secret));
    assert(!arm32_boot_secret_valid_v12(zero_secret));
    arm32_boot_secret_wipe_v12(secret);
    assert(memcmp(secret, zero_secret, sizeof secret) == 0);
    return 0;
}
