#include <stdio.h>

#include "cosmos_nvme_pcie_adapter_policy.h"
#include "cosmos_nvme_pcie_adapter_policy_oracle.h"

#define EXPECTED_PARITY_CASES 314U

#define PARITY(simple_value, oracle_value) do {                              \
    unsigned int simple_ = (unsigned int)(simple_value);                     \
    unsigned int oracle_ = (unsigned int)(oracle_value);                     \
    cases++;                                                                  \
    if (simple_ != oracle_) {                                                  \
        fprintf(stderr, "parity case %u: Simple=%08x oracle=%08x\n",       \
                cases, simple_, oracle_);                                     \
        return 1;                                                             \
    }                                                                         \
} while (0)

struct prp_vector {
    unsigned int low1;
    unsigned int high1;
    unsigned int low2;
    unsigned int high2;
    unsigned int bytes;
};

int main(void) {
    static const unsigned int words[] = {
        0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 15U, 512U, 768U,
        0xC0000000U, 0xFFFFFFFFU
    };
    static const struct prp_vector prps[] = {
        {0U, 0U, 0U, 0U, 4U},
        {0x1000U, 0U, 0U, 0U, 4U},
        {0x1000U, 0U, 0x2000U, 0U, 4U},
        {0x1FF0U, 0U, 0U, 0U, 32U},
        {0x1FF0U, 0U, 0x3000U, 0U, 32U},
        {0x1FF0U, 0U, 0x3004U, 0U, 32U},
        {0x1FF0U, 0U, 0x3010U, 0U, 8192U},
        {0x1FF0U, 0U, 0x3004U, 0U, 8192U},
        {0x1000U, 16U, 0U, 0U, 4U},
        {0x1004U, 0U, 0U, 0U, 4U},
        {0x1000U, 0U, 0U, 0U, 0U},
        {0x1000U, 0U, 0U, 0U, 1048577U}
    };
    unsigned int cases = 0U;
    unsigned int i;
    unsigned int a;
    unsigned int b;
    unsigned int c;
    unsigned int d;

    if (!cosmos_nvme_pcie_adapter_oracle_frozen_selfcheck()) {
        fputs("frozen adapter oracle self-check failed\n", stderr);
        return 1;
    }
    for (i = 0U; i < sizeof(words) / sizeof(words[0]); ++i) {
        unsigned int word = words[i];
        PARITY(cosmos_nvme_pcie_adapter_policy_command_cid(word),
               cosmos_nvme_pcie_adapter_oracle_command_cid(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_command_opcode(word),
               cosmos_nvme_pcie_adapter_oracle_command_opcode(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_block_bytes_valid(word),
               cosmos_nvme_pcie_adapter_oracle_block_bytes_valid(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_common_fields_supported(
                   word, word, word, word, word),
               cosmos_nvme_pcie_adapter_oracle_common_fields_supported(
                   word, word, word, word, word));
        PARITY(cosmos_nvme_pcie_adapter_policy_rw_fields_supported(
                   word, word, word, word),
               cosmos_nvme_pcie_adapter_oracle_rw_fields_supported(
                   word, word, word, word));
        PARITY(cosmos_nvme_pcie_adapter_policy_flush_fields_supported(
                   word, word, word, word, word, word, word, word,
                   word, word),
               cosmos_nvme_pcie_adapter_oracle_flush_fields_supported(
                   word, word, word, word, word, word, word, word,
                   word, word));
        PARITY(cosmos_nvme_pcie_adapter_policy_io_kind(word),
               cosmos_nvme_pcie_adapter_oracle_io_kind(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_io_nlb(word),
               cosmos_nvme_pcie_adapter_oracle_io_nlb(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_rw_control(word),
               cosmos_nvme_pcie_adapter_oracle_rw_control(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_write_zeroes_control(word),
               cosmos_nvme_pcie_adapter_oracle_write_zeroes_control(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_dsm_range_count(word),
               cosmos_nvme_pcie_adapter_oracle_dsm_range_count(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_dsm_attributes(word),
               cosmos_nvme_pcie_adapter_oracle_dsm_attributes(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_dsm_data_bytes(word),
               cosmos_nvme_pcie_adapter_oracle_dsm_data_bytes(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_admin_kind(word),
               cosmos_nvme_pcie_adapter_oracle_admin_kind(word));
        PARITY(cosmos_nvme_pcie_adapter_policy_admin_payload_bytes(
                   word & 3U, word),
               cosmos_nvme_pcie_adapter_oracle_admin_payload_bytes(
                   word & 3U, word));
    }

    PARITY(cosmos_nvme_pcie_adapter_policy_capacity_valid(0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_capacity_valid(0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_capacity_valid(0U, 1U),
           cosmos_nvme_pcie_adapter_oracle_capacity_valid(0U, 1U));
    PARITY(cosmos_nvme_pcie_adapter_policy_transfer_bytes(0xFFFFFFFFU, 512U),
           cosmos_nvme_pcie_adapter_oracle_transfer_bytes(0xFFFFFFFFU, 512U));
    PARITY(cosmos_nvme_pcie_adapter_policy_transfer_bytes(0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_transfer_bytes(0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_transfer_bytes(1U, 0xFFFFFFFFU),
           cosmos_nvme_pcie_adapter_oracle_transfer_bytes(1U, 0xFFFFFFFFU));
    PARITY(cosmos_nvme_pcie_adapter_policy_transfer_bytes(1U, 512U),
           cosmos_nvme_pcie_adapter_oracle_transfer_bytes(1U, 512U));
    PARITY(cosmos_nvme_pcie_adapter_policy_prp_first_bytes(0x1000U, 4U),
           cosmos_nvme_pcie_adapter_oracle_prp_first_bytes(0x1000U, 4U));
    PARITY(cosmos_nvme_pcie_adapter_policy_prp_first_bytes(0x1000U, 4096U),
           cosmos_nvme_pcie_adapter_oracle_prp_first_bytes(0x1000U, 4096U));

    for (i = 0U; i < sizeof(prps) / sizeof(prps[0]); ++i) {
        const struct prp_vector *v = &prps[i];
        PARITY(cosmos_nvme_pcie_adapter_policy_prp_span_valid(
                   v->low1, v->high1, v->low2, v->high2, v->bytes),
               cosmos_nvme_pcie_adapter_oracle_prp_span_valid(
                   v->low1, v->high1, v->low2, v->high2, v->bytes));
    }

    for (a = 0U; a <= 1U; ++a) {
        for (b = 0U; b <= 1U; ++b) {
            for (c = 0U; c <= 1U; ++c) {
                for (d = 0U; d <= 1U; ++d) {
                    PARITY(cosmos_nvme_pcie_adapter_policy_rw_decode_valid(
                               a, b, c, d),
                           cosmos_nvme_pcie_adapter_oracle_rw_decode_valid(
                               a, b, c, d));
                }
                PARITY(cosmos_nvme_pcie_adapter_policy_dsm_decode_valid(
                           a, b, c),
                       cosmos_nvme_pcie_adapter_oracle_dsm_decode_valid(
                           a, b, c));
            }
            PARITY(
                cosmos_nvme_pcie_adapter_policy_write_zeroes_decode_valid(a, b),
                cosmos_nvme_pcie_adapter_oracle_write_zeroes_decode_valid(a, b));
            PARITY(cosmos_nvme_pcie_adapter_policy_flush_decode_valid(a, b),
                   cosmos_nvme_pcie_adapter_oracle_flush_decode_valid(a, b));
            PARITY(cosmos_nvme_pcie_adapter_policy_admin_invalid_field(a, b),
                   cosmos_nvme_pcie_adapter_oracle_admin_invalid_field(a, b));
        }
    }

    PARITY(cosmos_nvme_pcie_adapter_policy_write_zeroes_fields_supported(
               0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_write_zeroes_fields_supported(
               0U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_write_zeroes_fields_supported(
               1U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_write_zeroes_fields_supported(
               1U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_dsm_fields_supported(
               0U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_dsm_fields_supported(
               0U, 0U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_dsm_fields_supported(
               0x100U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_dsm_fields_supported(
               0x100U, 0U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_common_fields_supported(
               0U, 0U, 0U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_admin_common_fields_supported(
               0U, 0U, 0U, 0U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_common_fields_supported(
               0x100U, 0U, 0U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_admin_common_fields_supported(
               0x100U, 0U, 0U, 0U, 0U, 0U, 0U));

    for (a = 0U; a <= 4U; ++a) {
        for (b = 0U; b <= 1U; ++b) {
            PARITY(cosmos_nvme_pcie_adapter_policy_io_invalid_field(a, b),
                   cosmos_nvme_pcie_adapter_oracle_io_invalid_field(a, b));
        }
    }

    PARITY(cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
               1U, 0x1000U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
               1U, 0x1000U, 0U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
               1U, 0x1004U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
               1U, 0x1004U, 0U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
               2U, 0x1000U, 0U, 0U, 0U, 4096U),
           cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
               2U, 0x1000U, 0U, 0U, 0U, 4096U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
               2U, 0U, 0U, 0U, 0U, 4096U),
           cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
               2U, 0U, 0U, 0U, 0U, 4096U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
               0U, 0U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
               0U, 0U, 0U, 0U, 0U, 0U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
               0U, 1U, 0U, 0U, 0U, 0U),
           cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
               0U, 1U, 0U, 0U, 0U, 0U));

    for (i = 0U; i <= 3U; ++i) {
        PARITY(cosmos_nvme_pcie_adapter_policy_post_result(i),
               cosmos_nvme_pcie_adapter_oracle_post_result(i));
    }
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_payload_request_valid(
               0x1000U, 0U, 0U, 4096U),
           cosmos_nvme_pcie_adapter_oracle_admin_payload_request_valid(
               0x1000U, 0U, 0U, 4096U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_payload_request_valid(
               0x1004U, 0U, 0U, 4096U),
           cosmos_nvme_pcie_adapter_oracle_admin_payload_request_valid(
               0x1004U, 0U, 0U, 4096U));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_payload_result(0),
           cosmos_nvme_pcie_adapter_oracle_admin_payload_result(0));
    PARITY(cosmos_nvme_pcie_adapter_policy_admin_payload_result(2),
           cosmos_nvme_pcie_adapter_oracle_admin_payload_result(2));
    PARITY(cosmos_nvme_pcie_adapter_policy_no_async_result(),
           cosmos_nvme_pcie_adapter_oracle_no_async_result());
    PARITY(cosmos_nvme_pcie_adapter_policy_init_values_valid(1U, 0U, 512U),
           cosmos_nvme_pcie_adapter_oracle_init_values_valid(1U, 0U, 512U));
    PARITY(cosmos_nvme_pcie_adapter_policy_init_values_valid(0U, 0U, 512U),
           cosmos_nvme_pcie_adapter_oracle_init_values_valid(0U, 0U, 512U));

    if (cases != EXPECTED_PARITY_CASES) {
        fprintf(stderr, "parity inventory: actual=%u required=%u\n",
                cases, EXPECTED_PARITY_CASES);
        return 1;
    }

    printf("COSMOS_NVME_PCIE_ADAPTER_C_ORACLE_PARITY_CASES %u\n", cases);
    return 0;
}
