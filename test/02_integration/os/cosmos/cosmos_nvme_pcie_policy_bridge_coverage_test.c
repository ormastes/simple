#include <stddef.h>

#include "cosmos_hal.h"
#include "cosmos_pcie_regs.h"

#define CHECK(value) do { if (!(value)) return 1; } while (0)

int main(void) {
    unsigned int word0;
    unsigned int word1;

    CHECK(cosmos_pcie_nvme_status_word(0U, 0U, 0U, NULL) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_status_word(8U, 0U, 0U, &word0) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_status_word(2U, 0x81U, 1U, &word0) == COSMOS_OK);
    CHECK(word0 == 0x8502U);

    CHECK(cosmos_pcie_nvme_io_sq_words(1U, 1U, 1U, 1U, 0x1000U, 0U,
        NULL, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_sq_words(1U, 1U, 1U, 1U, 0x1000U, 0U,
        &word0, NULL) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_sq_words(0U, 1U, 1U, 1U, 0x1000U, 0U,
        &word0, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_sq_words(1U, 1U, 2U, 64U, 0x12345000U, 10U,
        &word0, &word1) == COSMOS_OK);
    CHECK(word0 == 0x12345000U && word1 == 0x3F02800AU);

    CHECK(cosmos_pcie_nvme_io_cq_words(1U, 1U, 1U, 0U, 1U, 0x1000U, 0U,
        NULL, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_cq_words(1U, 1U, 1U, 0U, 1U, 0x1000U, 0U,
        &word0, NULL) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_cq_words(0U, 1U, 1U, 0U, 1U, 0x1000U, 0U,
        &word0, &word1) == COSMOS_INVALID);
    CHECK(cosmos_pcie_nvme_io_cq_words(1U, 1U, 1U, 0U, 64U, 0x12345000U, 10U,
        &word0, &word1) == COSMOS_OK);
    CHECK(word0 == 0x12345000U && word1 == 0x3F08800AU);
    return 0;
}
