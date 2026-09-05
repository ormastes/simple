/* Frozen, independent pre-migration C oracle for Cosmos boot decisions. */
#include "cosmos_boot_policy_oracle.h"

#define ORACLE_OK 0
#define ORACLE_UNAVAILABLE 1
#define ORACLE_INVALID 2
#define ORACLE_TIMEOUT 3
#define ORACLE_HW_ERROR 4
#define ORACLE_RETRY 5
#define ORACLE_EXCEPTION_CLEAR 0x434C4541U

int cosmos_boot_oracle_uart_should_attempt(
    unsigned int enabled_mask, unsigned int uart_bit) {
    return (enabled_mask & uart_bit) != 0U;
}

unsigned int cosmos_boot_oracle_uart_next_enabled(
    unsigned int enabled_mask, unsigned int uart_bit, int write_status) {
    return write_status == ORACLE_OK ? enabled_mask : enabled_mask & ~uart_bit;
}

int cosmos_boot_oracle_exception_should_capture(unsigned int active_state) {
    return active_state == ORACLE_EXCEPTION_CLEAR;
}

unsigned int cosmos_boot_oracle_exception_message_kind(unsigned int kind) {
    return kind == 1U ? 1U : 0U;
}

unsigned int cosmos_boot_oracle_status_kind(int status) {
    switch (status) {
        case ORACLE_OK: return 0U;
        case ORACLE_UNAVAILABLE: return 1U;
        case ORACLE_INVALID: return 2U;
        case ORACLE_TIMEOUT: return 3U;
        case ORACLE_HW_ERROR: return 4U;
        default: return 5U;
    }
}

int cosmos_boot_oracle_stage_allowed(int status) {
    return status == ORACLE_OK;
}

int cosmos_boot_oracle_software_ready(
    int runtime_status, int mmu_status, int gic_status, int policy_selftest) {
    return runtime_status == ORACLE_OK && mmu_status == ORACLE_OK &&
        gic_status == ORACLE_OK && policy_selftest != 0;
}

int cosmos_boot_oracle_handoff_allows_devices(
    int is_qemu, int software_ready, int fsbl_status) {
    return software_ready != 0 &&
        (is_qemu != 0 || fsbl_status == ORACLE_OK);
}

int cosmos_boot_oracle_selftest(int is_qemu) {
    if (is_qemu != 0) {
        int accepts_unavailable = cosmos_boot_oracle_handoff_allows_devices(
            1, 1, ORACLE_UNAVAILABLE);
        int rejects_failed_software =
            !cosmos_boot_oracle_handoff_allows_devices(1, 0, ORACLE_OK);
        return accepts_unavailable & rejects_failed_software;
    }
    {
        int accepts_ok = cosmos_boot_oracle_handoff_allows_devices(
            0, 1, ORACLE_OK);
        int rejects_unavailable = !cosmos_boot_oracle_handoff_allows_devices(
            0, 1, ORACLE_UNAVAILABLE);
        int rejects_failed_software =
            !cosmos_boot_oracle_handoff_allows_devices(0, 0, ORACLE_OK);
        return accepts_ok & rejects_unavailable & rejects_failed_software;
    }
}

int cosmos_boot_oracle_storage_init_allowed(int nfc_status, int pcie_status) {
    return nfc_status == ORACLE_OK && pcie_status == ORACLE_OK;
}

int cosmos_boot_oracle_secondary_release_allowed(
    int is_qemu, int handoff_allowed) {
    return is_qemu == 0 && handoff_allowed != 0;
}

unsigned int cosmos_boot_oracle_terminal_verdict(
    int is_qemu,
    int software_ready,
    int smp_status,
    int fsbl_status,
    int nfc_status,
    int pcie_status,
    int storage_status) {
    if (software_ready == 0) return 0U;
    if (is_qemu != 0) {
        return smp_status == ORACLE_UNAVAILABLE &&
            fsbl_status == ORACLE_UNAVAILABLE &&
            nfc_status == ORACLE_UNAVAILABLE &&
            pcie_status == ORACLE_UNAVAILABLE &&
            storage_status == ORACLE_UNAVAILABLE ? 1U : 0U;
    }
    return smp_status == ORACLE_OK && fsbl_status == ORACLE_OK &&
        nfc_status == ORACLE_OK && pcie_status == ORACLE_OK &&
        storage_status == ORACLE_OK ? 2U : 0U;
}

int cosmos_boot_oracle_irq_enable_allowed(int gic_status) {
    return gic_status == ORACLE_OK;
}

int cosmos_boot_oracle_storage_poll_allowed(int storage_status) {
    return storage_status == ORACLE_OK;
}

unsigned int cosmos_boot_oracle_storage_poll_action(int poll_status) {
    return poll_status == ORACLE_OK || poll_status == ORACLE_RETRY ? 0U : 1U;
}
