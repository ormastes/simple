#ifndef SIMPLE_COSMOS_NFC_POLICY_H
#define SIMPLE_COSMOS_NFC_POLICY_H

/* Scalar, allocation-free ABI emitted by cosmos_nfc_policy.spl.
 * cosmos_nfc.c retains all volatile DMA/MMIO, atomic, and pointer ownership. */
unsigned int cosmos_nfc_policy_channel_base(unsigned int channel);
int cosmos_nfc_policy_row_valid(unsigned int row_address);
int cosmos_nfc_policy_target_valid(unsigned int channel, unsigned int way,
                                   unsigned int row_address);
int cosmos_nfc_policy_erase_row_valid(unsigned int row_address);
int cosmos_nfc_policy_dma_range_valid(unsigned int address,
                                      unsigned int size,
                                      unsigned int base,
                                      unsigned int end,
                                      unsigned int stride,
                                      unsigned int contract_bound);
int cosmos_nfc_policy_data_valid(unsigned int address,
                                 unsigned int contract_bound);
int cosmos_nfc_policy_raw_data_valid(unsigned int address,
                                     unsigned int contract_bound);
int cosmos_nfc_policy_spare_valid(unsigned int address,
                                  unsigned int contract_bound);
int cosmos_nfc_policy_completion_valid(unsigned int address,
                                       unsigned int contract_bound);
int cosmos_nfc_policy_status_report_valid(unsigned int address,
                                          unsigned int contract_bound);
int cosmos_nfc_policy_error_info_valid(unsigned int address,
                                       unsigned int contract_bound);
int cosmos_nfc_policy_toggle_valid(unsigned int address,
                                   unsigned int contract_bound);
int cosmos_nfc_policy_ranges_overlap(unsigned int first,
                                     unsigned int first_size,
                                     unsigned int second,
                                     unsigned int second_size);
int cosmos_nfc_policy_dma_reserve_args_valid(unsigned int channel,
                                             unsigned int ranges_present,
                                             unsigned int count);
int cosmos_nfc_policy_dma_finish_releases(int status);
int cosmos_nfc_policy_channel_result_faults(int status);
unsigned int cosmos_nfc_policy_nand_status(unsigned int raw_report);
int cosmos_nfc_policy_decode_status(unsigned int raw_report);
int cosmos_nfc_policy_io_valid(int target_valid, int data_valid,
                               int spare_valid, int status_valid, int read,
                               int error_info_valid, int completion_valid);
int cosmos_nfc_policy_raw_io_valid(int target_valid, int raw_data_valid,
                                   int completion_valid, int status_valid);
int cosmos_nfc_policy_initialized_status(unsigned int initialized);
int cosmos_nfc_policy_contract_status(int contract_status);
int cosmos_nfc_policy_locked_channel_status(unsigned int faulted,
                                            int contract_status);
int cosmos_nfc_policy_init_state_status(unsigned int initialized,
                                        unsigned int init_failed);
int cosmos_nfc_policy_init_selftest_status(int selftest_status);
int cosmos_nfc_policy_init_contract_status(int contract_status);
int cosmos_nfc_policy_raw_completion_status(unsigned int completion_word);
unsigned int cosmos_nfc_policy_toggle_payload_word(unsigned int index);

#endif
