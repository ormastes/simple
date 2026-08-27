#include <stdio.h>
#include <string.h>

#include "cosmos_nfc_regs.h"

static int legacy_c_oracle(const volatile unsigned int *error_info,
                           struct cosmos_nfc_ecc *ecc) {
    unsigned int first;
    if (error_info == 0 || ecc == 0) {
        return COSMOS_INVALID;
    }
    first = error_info[0];
    ecc->crc_valid = (first & COSMOS_NFC_ECC_CRC_VALID) != 0U;
    ecc->spare_valid = (first & COSMOS_NFC_ECC_SPARE_VALID) != 0U;
    ecc->page_valid = error_info[1] == 0xFFFFFFFFU;
    ecc->worst_chunk_errors =
        (first & COSMOS_NFC_ECC_WORST_MASK) >> COSMOS_NFC_ECC_WORST_SHIFT;
    ecc->needs_refresh =
        ecc->worst_chunk_errors > COSMOS_NFC_ECC_WARNING_THRESHOLD;
    return ecc->crc_valid && ecc->spare_valid && ecc->page_valid ?
        COSMOS_OK : COSMOS_HW_ERROR;
}

static int compare_case(unsigned int first, unsigned int page_word) {
    volatile unsigned int words[COSMOS_NFC_ERROR_INFO_WORDS] = {
        first, page_word
    };
    struct cosmos_nfc_ecc expected;
    struct cosmos_nfc_ecc actual;
    int expected_status;
    int actual_status;

    memset(&expected, 0xA5, sizeof(expected));
    memset(&actual, 0x5A, sizeof(actual));
    expected_status = legacy_c_oracle(words, &expected);
    actual_status = cosmos_nfc_decode_ecc(words, &actual);
    if (expected_status != actual_status ||
        memcmp(&expected, &actual, sizeof(expected)) != 0) {
        fprintf(stderr,
                "FAIL first=%08x page=%08x expected_status=%d actual_status=%d\n",
                first, page_word, expected_status, actual_status);
        return 1;
    }
    return 0;
}

int main(void) {
    static const unsigned int page_words[] = {
        0xFFFFFFFFU, 0xFFFFFFFEU, 0U
    };
    static const unsigned int unrelated_bits[] = {
        0U, 0x80008001U
    };
    unsigned int crc;
    unsigned int spare;
    unsigned int errors;
    unsigned int page_index;
    unsigned int unrelated_index;
    unsigned int cases = 0U;

    if (cosmos_nfc_decode_ecc(0, 0) != COSMOS_INVALID) {
        return 1;
    }
    {
        volatile unsigned int words[COSMOS_NFC_ERROR_INFO_WORDS] = {0U};
        struct cosmos_nfc_ecc ecc;
        if (cosmos_nfc_decode_ecc(words, 0) != COSMOS_INVALID) {
            return 1;
        }
        if (cosmos_nfc_decode_ecc(0, &ecc) != COSMOS_INVALID) {
            return 1;
        }
    }
    for (crc = 0U; crc <= 1U; crc++) {
        for (spare = 0U; spare <= 1U; spare++) {
            for (errors = 0U; errors <= 255U; errors++) {
                for (page_index = 0U;
                     page_index < sizeof(page_words) / sizeof(page_words[0]);
                     page_index++) {
                    for (unrelated_index = 0U;
                         unrelated_index < sizeof(unrelated_bits) /
                            sizeof(unrelated_bits[0]);
                         unrelated_index++) {
                        unsigned int first =
                            (crc != 0U ? COSMOS_NFC_ECC_CRC_VALID : 0U) |
                            (spare != 0U ? COSMOS_NFC_ECC_SPARE_VALID : 0U) |
                            (errors << COSMOS_NFC_ECC_WORST_SHIFT) |
                            unrelated_bits[unrelated_index];
                        if (compare_case(first, page_words[page_index]) != 0) {
                            return 1;
                        }
                        cases++;
                    }
                }
            }
        }
    }
    printf("COSMOS_NFC_ECC_C_ORACLE_CASES %u\n", cases);
    puts("STATUS: PASS cosmos-nfc-ecc C-oracle parity");
    return 0;
}
