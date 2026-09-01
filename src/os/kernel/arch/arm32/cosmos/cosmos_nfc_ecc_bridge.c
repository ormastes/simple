/* Volatile DMA acquisition and established C ABI bridge for the pure-Simple
 * Cosmos+ ECC policy. No ECC interpretation is permitted in this file. */
#include "cosmos_nfc_ecc_policy.h"
#include "cosmos_nfc_regs.h"

int cosmos_nfc_decode_ecc(const volatile unsigned int *error_info,
                          struct cosmos_nfc_ecc *ecc) {
    unsigned int first;
    unsigned int page_word;

    if (error_info == 0 || ecc == 0) {
        return COSMOS_INVALID;
    }
    first = error_info[0];
    page_word = error_info[1];
    ecc->crc_valid = cosmos_nfc_ecc_policy_crc_valid(first);
    ecc->spare_valid = cosmos_nfc_ecc_policy_spare_valid(first);
    ecc->page_valid = cosmos_nfc_ecc_policy_page_valid(page_word);
    ecc->worst_chunk_errors =
        cosmos_nfc_ecc_policy_worst_chunk_errors(first);
    ecc->needs_refresh = cosmos_nfc_ecc_policy_needs_refresh(first);
    return cosmos_nfc_ecc_policy_status(first, page_word);
}
