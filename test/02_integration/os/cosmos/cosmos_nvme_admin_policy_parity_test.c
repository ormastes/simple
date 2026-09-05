#include <stdio.h>

#include "cosmos_nvme_admin_policy.h"
#include "cosmos_nvme_admin_policy_oracle.h"

#define CHECK_PARITY(simple_value, oracle_value) do {                        \
    unsigned int simple_result_ = (simple_value);                            \
    unsigned int oracle_result_ = (oracle_value);                            \
    cases++;                                                                  \
    if (simple_result_ != oracle_result_) {                                   \
        fprintf(stderr, "parity case %u: Simple=%08x oracle=%08x\n",        \
                cases, simple_result_, oracle_result_);                       \
        return 1;                                                             \
    }                                                                         \
} while (0)

int main(void) {
    static const unsigned int nsids[] = {0U, 1U, 2U, 0xFFFFFFFFU};
    static const unsigned int words[] = {
        0U, 1U, 2U, 7U, 0x80000007U, 0x007F0002U,
        0x007E0002U, 0x10000001U
    };
    static const unsigned int tails[] = {0U, 1U, 0xFFFFFFFFU};
    unsigned int cases = 0U;
    unsigned int ni;
    unsigned int wi;
    unsigned int ti;
    unsigned int negotiated;
    unsigned int flag;

    if (!cosmos_nvme_admin_oracle_frozen_selfcheck()) {
        fputs("frozen oracle self-check failed\n", stderr);
        return 1;
    }

    for (ni = 0U; ni < sizeof(nsids) / sizeof(nsids[0]); ni++) {
        for (wi = 0U; wi < sizeof(words) / sizeof(words[0]); wi++) {
            for (ti = 0U; ti < sizeof(tails) / sizeof(tails[0]); ti++) {
                CHECK_PARITY(cosmos_nvme_admin_policy_identify_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U),
                    cosmos_nvme_admin_oracle_identify_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U));
                CHECK_PARITY(cosmos_nvme_admin_policy_get_log_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U),
                    cosmos_nvme_admin_oracle_get_log_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U));
                CHECK_PARITY(cosmos_nvme_admin_policy_set_features_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U),
                    cosmos_nvme_admin_oracle_set_features_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U));
                CHECK_PARITY(cosmos_nvme_admin_policy_get_features_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U),
                    cosmos_nvme_admin_oracle_get_features_status(
                    nsids[ni], words[wi], tails[ti], 0U, 0U));
            }
        }
    }

    for (negotiated = 0U; negotiated <= 5U; negotiated++) {
        for (flag = 0U; flag <= 1U; flag++) {
            CHECK_PARITY(cosmos_nvme_admin_policy_create_cq_status(
                negotiated, flag, 0U, 1U, 3U, 0U, 0U,
                0x1000U, 0U, 0U, 0U, 0U),
                cosmos_nvme_admin_oracle_create_cq_status(
                negotiated, flag, 0U, 1U, 3U, 0U, 0U,
                0x1000U, 0U, 0U, 0U, 0U));
            CHECK_PARITY(cosmos_nvme_admin_policy_create_sq_status(
                negotiated, flag, 0U, 0U, 1U, 0x00010001U, 0U, 0U,
                0x1000U, 0U, 0U, 0U, 0U),
                cosmos_nvme_admin_oracle_create_sq_status(
                negotiated, flag, 0U, 0U, 1U, 0x00010001U, 0U, 0U,
                0x1000U, 0U, 0U, 0U, 0U));
            CHECK_PARITY(cosmos_nvme_admin_policy_delete_sq_status(
                negotiated, flag, 0U, 1U, 0U, 0U, 0U,
                0U, 0U, 0U, 0U, 0U),
                cosmos_nvme_admin_oracle_delete_sq_status(
                negotiated, flag, 0U, 1U, 0U, 0U, 0U,
                0U, 0U, 0U, 0U, 0U));
            CHECK_PARITY(cosmos_nvme_admin_policy_delete_cq_status(
                negotiated, 1U, flag, 0U, 1U, 0U, 0U, 0U,
                0U, 0U, 0U, 0U, 0U),
                cosmos_nvme_admin_oracle_delete_cq_status(
                negotiated, 1U, flag, 0U, 1U, 0U, 0U, 0U,
                0U, 0U, 0U, 0U, 0U));
            CHECK_PARITY(cosmos_nvme_admin_policy_abort_status(
                negotiated, flag, 0U, 0x00010007U, 0U, 0U, 0U),
                cosmos_nvme_admin_oracle_abort_status(
                negotiated, flag, 0U, 0x00010007U, 0U, 0U, 0U));
        }
    }

    for (wi = 0U; wi < sizeof(words) / sizeof(words[0]); wi++) {
        CHECK_PARITY(cosmos_nvme_admin_policy_envelope_status(
            0U, 0U, 1U, words[wi], 4U, 0U, 0U, 0U, 4U),
            cosmos_nvme_admin_oracle_envelope_status(
            0U, 0U, 1U, words[wi], 4U, 0U, 0U, 0U, 4U));
        CHECK_PARITY(cosmos_nvme_admin_policy_async_event_status(
            1U, words[wi] != 0U, 0U, 0U, 0U, 0U, 0U),
            cosmos_nvme_admin_oracle_async_event_status(
            1U, words[wi] != 0U, 0U, 0U, 0U, 0U, 0U));
    }

    printf("COSMOS_NVME_ADMIN_C_ORACLE_PARITY_CASES %u\n", cases);
    return 0;
}
