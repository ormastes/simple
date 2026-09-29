#include <stdio.h>

#include "cosmos_mmu_cache_policy.h"
#include "cosmos_mmu_cache_policy_oracle.h"

#define COUNT(values) (sizeof(values) / sizeof((values)[0]))
#define CHECK_EQ(label, oracle_expression, simple_expression) do { \
    unsigned int oracle_value_ = (unsigned int)(oracle_expression); \
    unsigned int simple_value_ = (unsigned int)(simple_expression); \
    cases++; \
    if (oracle_value_ != simple_value_) { \
        fprintf(stderr, "parity mismatch %s case=%u oracle=%u simple=%u\n", \
            (label), cases, oracle_value_, simple_value_); \
        return 1; \
    } \
} while (0)

int main(void) {
    static const unsigned int values[] = {
        0U, 1U, 2U, 3U, 4U, 7U, 8U, 15U, 16U, 31U, 32U, 63U, 64U,
        255U, 256U, 1023U, 1024U, 4095U, 4096U, 4097U, 65535U,
        65536U, 0x000FFFFFU, 0x00100000U, 0x00107FFFU, 0x00108000U,
        0x001FFFFFU, 0x00200000U, 0x17FFFFFFU, 0x18000000U,
        0x3FFFFFFFU, 0x40000000U, 0x43C00000U, 0x70000000U,
        0x83C00000U, 0xE0000000U, 0xF8000000U, 0xF8F00000U,
        0xFFEFFFFFU, 0xFFF00000U, 0xFFFBFFFFU, 0xFFFC0000U, 0xFFFFFFFFU
    };
    static const unsigned int levels[] = {0U, 1U, 7U};
    static const unsigned int coordinates[] = {0U, 1U, 3U, 0xFFFFFFFFU};
    static const unsigned int shifts[] = {0U, 1U, 5U, 29U, 31U};
    static const unsigned int bits[] = {0U, 1U, 0x40U, 0xFFFFFFFFU};
    static const unsigned int pairs[] = {0U, 1U};
    static const unsigned int attributes[] = {
        0U, 0x00001008U, 0x00011010U, 0x0001101CU,
        0xFFFFFFFFU, 0x80000000U
    };
    static const unsigned int rx_ends[] = {
        0U, 0x00100000U, 0x00100001U,
        0x00107FFFU, 0x00108000U, 0xFFFFFFFFU
    };
    static const unsigned int tables[] = {0U, 0x12345000U, 0xFFFFFFFFU};
    unsigned int cases = 0U;
    unsigned int a, b, c, d, e, f;

    for (a = 0U; a < COUNT(values); ++a) {
        unsigned int value = values[a];
        CHECK_EQ("cache-way-shift",
            cosmos_mmu_cache_oracle_cache_way_shift(value),
            cosmos_mmu_cache_policy_cache_way_shift(value));
        CHECK_EQ("ttbr0",
            cosmos_mmu_cache_oracle_ttbr0_value(value),
            cosmos_mmu_cache_policy_ttbr0_value(value));
        CHECK_EQ("sctlr-apply",
            cosmos_mmu_cache_oracle_sctlr_apply_policy(value),
            cosmos_mmu_cache_policy_sctlr_apply_policy(value));
        CHECK_EQ("sctlr-valid",
            cosmos_mmu_cache_oracle_sctlr_policy_valid(value),
            cosmos_mmu_cache_policy_sctlr_policy_valid(value));
        CHECK_EQ("scu-mask",
            cosmos_mmu_cache_oracle_scu_invalidate_mask(value),
            cosmos_mmu_cache_policy_scu_invalidate_mask(value));
        CHECK_EQ("coarse",
            cosmos_mmu_cache_oracle_coarse_descriptor(value),
            cosmos_mmu_cache_policy_coarse_descriptor(value));
        CHECK_EQ("small-page",
            cosmos_mmu_cache_oracle_small_page_descriptor(value),
            cosmos_mmu_cache_policy_small_page_descriptor(value));
        CHECK_EQ("small-page-rx",
            cosmos_mmu_cache_oracle_small_page_cached_rx_descriptor(value),
            cosmos_mmu_cache_policy_small_page_cached_rx_descriptor(value));
        CHECK_EQ("small-page-rw-xn",
            cosmos_mmu_cache_oracle_small_page_cached_rw_xn_descriptor(value),
            cosmos_mmu_cache_policy_small_page_cached_rw_xn_descriptor(value));
        CHECK_EQ("l2-executable",
            cosmos_mmu_cache_oracle_l2_descriptor_executable(value),
            cosmos_mmu_cache_policy_l2_descriptor_executable(value));
        CHECK_EQ("l2-writable",
            cosmos_mmu_cache_oracle_l2_descriptor_priv_writable(value),
            cosmos_mmu_cache_policy_l2_descriptor_priv_writable(value));
        CHECK_EQ("l2-write-execute",
            cosmos_mmu_cache_oracle_l2_descriptor_write_execute(value),
            cosmos_mmu_cache_policy_l2_descriptor_write_execute(value));
        CHECK_EQ("device-section",
            cosmos_mmu_cache_oracle_device_section(value),
            cosmos_mmu_cache_policy_device_section(value));
        CHECK_EQ("ocm-l2",
            cosmos_mmu_cache_oracle_ocm_l2_descriptor_for_address(value),
            cosmos_mmu_cache_policy_ocm_l2_descriptor_for_address(value));
        CHECK_EQ("poll",
            cosmos_mmu_cache_oracle_mmu_poll_allowed(value),
            cosmos_mmu_cache_policy_mmu_poll_allowed(value));
        for (b = 0U; b < COUNT(attributes); ++b) {
            CHECK_EQ("section",
                cosmos_mmu_cache_oracle_section_descriptor(
                    value, attributes[b]),
                cosmos_mmu_cache_policy_section_descriptor(
                    value, attributes[b]));
        }
        for (b = 0U; b < COUNT(rx_ends); ++b) {
            CHECK_EQ("firmware-l2",
                cosmos_mmu_cache_oracle_firmware_l2_descriptor_for_address(
                    value, rx_ends[b]),
                cosmos_mmu_cache_policy_firmware_l2_descriptor_for_address(
                    value, rx_ends[b]));
        }
        for (b = 0U; b < COUNT(tables); ++b) {
            for (c = 0U; c < COUNT(tables); ++c) {
                CHECK_EQ("l1",
                    cosmos_mmu_cache_oracle_l1_descriptor_for_address(
                        value, tables[b], tables[c]),
                    cosmos_mmu_cache_policy_l1_descriptor_for_address(
                        value, tables[b], tables[c]));
            }
        }
    }

    for (a = 0U; a < COUNT(levels); ++a)
    for (b = 0U; b < COUNT(coordinates); ++b)
    for (c = 0U; c < COUNT(coordinates); ++c)
    for (d = 0U; d < COUNT(shifts); ++d)
    for (e = 0U; e < COUNT(shifts); ++e) {
        CHECK_EQ("setway",
            cosmos_mmu_cache_oracle_cache_setway_operand(
                levels[a], coordinates[b], coordinates[c], shifts[d], shifts[e]),
            cosmos_mmu_cache_policy_cache_setway_operand(
                levels[a], coordinates[b], coordinates[c], shifts[d], shifts[e]));
    }

    for (a = 0U; a < COUNT(pairs); ++a)
    for (b = 0U; b < COUNT(pairs); ++b)
    for (c = 0U; c < COUNT(pairs); ++c)
    for (d = 0U; d < COUNT(pairs); ++d)
    for (e = 0U; e < COUNT(pairs); ++e)
    for (f = 0U; f < COUNT(pairs); ++f) {
        CHECK_EQ("control-registers",
            cosmos_mmu_cache_oracle_control_registers_valid(
                pairs[a], pairs[b], pairs[c], pairs[d], pairs[e],
                pairs[f] == 0U ? 0U : 0x00001005U),
            cosmos_mmu_cache_policy_control_registers_valid(
                pairs[a], pairs[b], pairs[c], pairs[d], pairs[e],
                pairs[f] == 0U ? 0U : 0x00001005U));
    }

    CHECK_EQ("control-contract",
        cosmos_mmu_cache_oracle_control_policy_contract(),
        cosmos_mmu_cache_policy_control_policy_contract());

    for (a = 0U; a < COUNT(bits); ++a) {
        for (b = 0U; b < COUNT(bits); ++b) {
            CHECK_EQ("cache-enable",
                cosmos_mmu_cache_oracle_cache_enable_allowed(bits[a], bits[b]),
                cosmos_mmu_cache_policy_cache_enable_allowed(bits[a], bits[b]));
        }
    }

    if (cases != 2829U) {
        fprintf(stderr, "unexpected parity case count: %u\n", cases);
        return 1;
    }
    printf("COSMOS_MMU_C_ORACLE_PARITY_CASES %u\n", cases);
    return 0;
}
