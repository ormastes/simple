#ifndef SIMPLE_COSMOS_BOOT_POLICY_H
#define SIMPLE_COSMOS_BOOT_POLICY_H

#define COSMOS_BOOT_STATUS_OK 0U
#define COSMOS_BOOT_STATUS_UNAVAILABLE 1U
#define COSMOS_BOOT_STATUS_INVALID 2U
#define COSMOS_BOOT_STATUS_TIMEOUT 3U
#define COSMOS_BOOT_STATUS_HW_ERROR 4U
#define COSMOS_BOOT_STATUS_UNKNOWN 5U

#define COSMOS_BOOT_EXCEPTION_DATA 0U
#define COSMOS_BOOT_EXCEPTION_PREFETCH 1U

#define COSMOS_BOOT_VERDICT_FAIL 0U
#define COSMOS_BOOT_VERDICT_SOFTWARE 1U
#define COSMOS_BOOT_VERDICT_SILICON 2U

#define COSMOS_BOOT_POLL_CONTINUE 0U
#define COSMOS_BOOT_POLL_FAIL 1U

void cosmos_boot_policy_coverage_reset(void);
unsigned long long cosmos_boot_policy_coverage_low(void);
unsigned long long cosmos_boot_policy_coverage_high(void);
unsigned long long cosmos_boot_policy_coverage_required_low(void);
unsigned long long cosmos_boot_policy_coverage_required_high(void);
unsigned int cosmos_boot_policy_coverage_decisions(void);

int cosmos_boot_policy_uart_should_attempt(
    unsigned int enabled_mask, unsigned int uart_bit);
unsigned int cosmos_boot_policy_uart_next_enabled(
    unsigned int enabled_mask, unsigned int uart_bit, int write_status);
int cosmos_boot_policy_exception_should_capture(unsigned int active_state);
unsigned int cosmos_boot_policy_exception_message_kind(unsigned int kind);
unsigned int cosmos_boot_policy_status_kind(int status);
int cosmos_boot_policy_stage_allowed(int status);
int cosmos_boot_policy_software_ready(
    int runtime_status, int mmu_status, int gic_status, int policy_selftest);
int cosmos_boot_policy_selftest(int is_qemu);
int cosmos_boot_policy_handoff_allows_devices(
    int is_qemu, int software_ready, int fsbl_status);
int cosmos_boot_policy_storage_init_allowed(int nfc_status, int pcie_status);
int cosmos_boot_policy_secondary_release_allowed(
    int is_qemu, int handoff_allowed);
unsigned int cosmos_boot_policy_terminal_verdict(
    int is_qemu,
    int software_ready,
    int smp_status,
    int fsbl_status,
    int nfc_status,
    int pcie_status,
    int storage_status);
int cosmos_boot_policy_irq_enable_allowed(int gic_status);
int cosmos_boot_policy_storage_poll_allowed(int storage_status);
unsigned int cosmos_boot_policy_storage_poll_action(int poll_status);

#endif
