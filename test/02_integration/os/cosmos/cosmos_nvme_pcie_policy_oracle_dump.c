#include <stdio.h>

#include "cosmos_nvme_pcie_policy.h"

int main(void) {
    static const unsigned int status_values[] = {0U, 1U, 7U, 8U, 255U, 256U};
    static const unsigned int ids[] = {0U, 1U, 8U, 9U};
    static const unsigned int flags[] = {0U, 1U, 2U};
    static const unsigned int entries_values[] = {0U, 1U, 256U, 257U};
    static const unsigned int lows[] = {0U, 0x1000U, 0x1004U};
    static const unsigned int highs[] = {0U, 15U, 16U};
    unsigned int a, b, c, d, e, f, g;

    for (a = 0U; a < 6U; ++a) {
        for (b = 0U; b < 6U; ++b) {
            for (c = 0U; c < 3U; ++c) {
                unsigned int sct = status_values[a];
                unsigned int sc = status_values[b];
                unsigned int dnr = flags[c];
                printf("P|status|%u|%u|%u|%d|%u\n", sct, sc, dnr,
                    cosmos_nvme_pcie_policy_status_fields_valid(sct, sc, dnr),
                    cosmos_nvme_pcie_policy_status_word(sct, sc, dnr));
            }
        }
    }
    for (a = 0U; a < 4U; ++a) for (b = 0U; b < 3U; ++b)
    for (c = 0U; c < 4U; ++c) for (d = 0U; d < 4U; ++d)
    for (e = 0U; e < 3U; ++e) for (f = 0U; f < 3U; ++f) {
        printf("P|sq|%u|%u|%u|%u|%u|%u|%d|%u\n",
            ids[a], flags[b], ids[c], entries_values[d], lows[e], highs[f],
            cosmos_nvme_pcie_policy_io_sq_valid(
                ids[a], flags[b], ids[c], entries_values[d], lows[e], highs[f]),
            cosmos_nvme_pcie_policy_io_sq_word1(
                flags[b], ids[c], entries_values[d], highs[f]));
    }
    for (a = 0U; a < 4U; ++a) for (b = 0U; b < 3U; ++b)
    for (c = 0U; c < 3U; ++c) for (d = 0U; d < 3U; ++d)
    for (e = 0U; e < 4U; ++e) for (f = 0U; f < 3U; ++f)
    for (g = 0U; g < 3U; ++g) {
        printf("P|cq|%u|%u|%u|%u|%u|%u|%u|%d|%u\n",
            ids[a], flags[b], flags[c], status_values[d], entries_values[e],
            lows[f], highs[g],
            cosmos_nvme_pcie_policy_io_cq_valid(
                ids[a], flags[b], flags[c], status_values[d], entries_values[e],
                lows[f], highs[g]),
            cosmos_nvme_pcie_policy_io_cq_word1(
                flags[b], flags[c], status_values[d], entries_values[e], highs[g]));
    }
    return 0;
}
