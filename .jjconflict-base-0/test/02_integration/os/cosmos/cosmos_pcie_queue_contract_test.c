#include <stdio.h>

#include "cosmos_hal.h"
#include "cosmos_pcie_regs.h"

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                    \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

int main(void) {
    unsigned int word0;
    unsigned int word1;

    CHECK(cosmos_pcie_nvme_io_sq_words(
              1U, 1U, 2U, 64U, 0x12345000U, 0xAU,
              &word0, &word1) == COSMOS_OK);
    CHECK(word0 == 0x12345000U);
    CHECK(word1 == 0x3F02800AU);
    CHECK(cosmos_pcie_nvme_io_cq_words(
              1U, 1U, 1U, 0U, 64U, 0x12345000U, 0xAU,
              &word0, &word1) == COSMOS_OK);
    CHECK(word0 == 0x12345000U);
    CHECK(word1 == 0x3F08800AU);

    CHECK(cosmos_pcie_nvme_io_sq_words(
              0U, 1U, 1U, 64U, 0x1000U, 0U,
              &word0, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_sq_words(
              1U, 1U, 1U, 257U, 0x1000U, 0U,
              &word0, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_cq_words(
              1U, 1U, 1U, 8U, 64U, 0x1000U, 0U,
              &word0, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_cq_words(
              1U, 1U, 0U, 0U, 64U, 0x1004U, 0U,
              &word0, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_configure_io_sq(
              0U, 1U, 1U, 64U, 0x1000U, 0U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_configure_io_sq(
              1U, 1U, 1U, 64U, 0x1000U, 0U) == COSMOS_UNAVAILABLE);
    puts("cosmos PCIe queue contract: PASS");
    return 0;
}
