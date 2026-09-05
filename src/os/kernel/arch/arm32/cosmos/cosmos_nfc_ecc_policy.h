#ifndef SIMPLE_COSMOS_NFC_ECC_POLICY_H
#define SIMPLE_COSMOS_NFC_ECC_POLICY_H

/* Internal scalar ABI emitted by cosmos_nfc_ecc.spl. The public NAND ABI
 * remains cosmos_nfc_decode_ecc() from cosmos_nfc_regs.h. */
unsigned int cosmos_nfc_ecc_policy_crc_valid(unsigned int first);
unsigned int cosmos_nfc_ecc_policy_spare_valid(unsigned int first);
unsigned int cosmos_nfc_ecc_policy_page_valid(unsigned int page_word);
unsigned int cosmos_nfc_ecc_policy_worst_chunk_errors(unsigned int first);
unsigned int cosmos_nfc_ecc_policy_needs_refresh(unsigned int first);
int cosmos_nfc_ecc_policy_status(unsigned int first,
                                 unsigned int page_word);

#endif
