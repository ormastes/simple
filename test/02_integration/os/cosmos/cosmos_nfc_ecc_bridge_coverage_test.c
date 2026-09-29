#include <stdio.h>

#include "cosmos_nfc_regs.h"

/* Deterministic bridge seams only. These are not an ECC policy oracle. */
unsigned int cosmos_nfc_ecc_policy_crc_valid(unsigned int first) {
    return first;
}

unsigned int cosmos_nfc_ecc_policy_spare_valid(unsigned int first) {
    return first + 1U;
}

unsigned int cosmos_nfc_ecc_policy_page_valid(unsigned int page_word) {
    return page_word;
}

unsigned int cosmos_nfc_ecc_policy_worst_chunk_errors(unsigned int first) {
    return first + 2U;
}

unsigned int cosmos_nfc_ecc_policy_needs_refresh(unsigned int first) {
    return first + 3U;
}

int cosmos_nfc_ecc_policy_status(unsigned int first,
                                 unsigned int page_word) {
    return first == 7U && page_word == 11U ? COSMOS_OK : COSMOS_HW_ERROR;
}

int main(void) {
    volatile unsigned int words[COSMOS_NFC_ERROR_INFO_WORDS] = {7U, 11U};
    struct cosmos_nfc_ecc ecc;

    if (cosmos_nfc_decode_ecc(0, 0) != COSMOS_INVALID ||
        cosmos_nfc_decode_ecc(words, 0) != COSMOS_INVALID ||
        cosmos_nfc_decode_ecc(0, &ecc) != COSMOS_INVALID) {
        return 1;
    }
    if (cosmos_nfc_decode_ecc(words, &ecc) != COSMOS_OK ||
        ecc.crc_valid != 7U || ecc.spare_valid != 8U ||
        ecc.page_valid != 11U || ecc.worst_chunk_errors != 9U ||
        ecc.needs_refresh != 10U) {
        return 1;
    }
    puts("STATUS: PASS cosmos-nfc-ecc acquisition bridge behavior");
    return 0;
}
