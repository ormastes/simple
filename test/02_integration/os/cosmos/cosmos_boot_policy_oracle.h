#ifndef SIMPLE_COSMOS_BOOT_POLICY_ORACLE_H
#define SIMPLE_COSMOS_BOOT_POLICY_ORACLE_H

int cosmos_boot_oracle_uart_should_attempt(
    unsigned int enabled_mask, unsigned int uart_bit);
unsigned int cosmos_boot_oracle_uart_next_enabled(
    unsigned int enabled_mask, unsigned int uart_bit, int write_status);
int cosmos_boot_oracle_exception_should_capture(unsigned int active_state);
unsigned int cosmos_boot_oracle_exception_message_kind(unsigned int kind);
unsigned int cosmos_boot_oracle_status_kind(int status);
int cosmos_boot_oracle_stage_allowed(int status);
int cosmos_boot_oracle_software_ready(
    int runtime_status, int mmu_status, int gic_status, int policy_selftest);
int cosmos_boot_oracle_selftest(int is_qemu);
int cosmos_boot_oracle_handoff_allows_devices(
    int is_qemu, int software_ready, int fsbl_status);
int cosmos_boot_oracle_storage_init_allowed(int nfc_status, int pcie_status);
int cosmos_boot_oracle_secondary_release_allowed(
    int is_qemu, int handoff_allowed);
unsigned int cosmos_boot_oracle_terminal_verdict(
    int is_qemu,
    int software_ready,
    int smp_status,
    int fsbl_status,
    int nfc_status,
    int pcie_status,
    int storage_status);
int cosmos_boot_oracle_irq_enable_allowed(int gic_status);
int cosmos_boot_oracle_storage_poll_allowed(int storage_status);
unsigned int cosmos_boot_oracle_storage_poll_action(int poll_status);

#endif
