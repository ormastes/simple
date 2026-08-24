#define rt_pci_device_count rt_desktop_pci_device_count
#define rt_pci_get_field rt_desktop_pci_get_field
#define rt_net_init rt_desktop_pci_net_init
#define rt_net_tx_test rt_desktop_pci_net_tx_test
#define rt_net_rx_ready rt_desktop_pci_net_rx_ready
#define rt_net_stats rt_desktop_pci_net_stats
#define rt_net_debug_stage rt_desktop_pci_net_debug_stage
#define rt_net_debug_queue_max rt_desktop_pci_net_debug_queue_max
#define rt_boot_tcp_bind_port rt_desktop_pci_boot_tcp_bind_port
#define rt_boot_tcp_accept_timeout rt_desktop_pci_boot_tcp_accept_timeout
#define rt_boot_tcp_write_auto rt_desktop_pci_boot_tcp_write_auto
#define rt_boot_tcp_send_ssh_banner rt_desktop_pci_boot_tcp_send_ssh_banner
#define rt_boot_tcp_close rt_desktop_pci_boot_tcp_close
#define rt_display_init rt_desktop_pci_display_init
#define rt_display_flush_test rt_desktop_pci_display_flush_test
#define rt_display_width rt_desktop_pci_display_width
#define rt_display_height rt_desktop_pci_display_height
#include "../../../../../../src/os/kernel/arch/riscv64/boot/freestanding_runtime.c"

spl_i64 rt_riscv_harden_canary_value(void) {
    return 0x5a17d35c;
}

/* ---------------------------------------------------------------------------
 * FABRICATION FENCE (2026-08-24)
 *
 * The five `rt_riscv_*` probes below have NO implementation. They previously
 * read `return 1;` -- an unconditional SUCCESS -- so every caller printed its
 * ok-shaped marker (`[riscv-nvfs] image read ok`, `FS_MOUNT_OK`,
 * `SMF_DISCOVERY_OK`, `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_GUI_LAUNCH_OK`,
 * `NATIVE_GUI_RENDER_OK`) on every boot regardless of whether the underlying
 * capability existed. Those markers were cited in bug records and in the
 * hardening plan as proof that nvfs / SMF discovery / SMF launch worked. They
 * proved nothing: they were a constant.
 *
 * They are NOT deleted -- `simpleos_riscv64_smf_fs.elf` needs the symbols to
 * link, and the entries reference them via `extern fn`. Instead each one now
 * announces itself on the serial console as `STUBBED <name>` and returns 0
 * (failure), so a transcript can never again be read as evidence of a
 * capability that was never written. Replacing a stub with a real
 * implementation means deleting its `rt_riscv_stub_announce` call AND its row
 * in `config/simpleos_fabricated_rt_baseline.sdn` in the same commit.
 * Never restore `return 1;`.
 * ------------------------------------------------------------------------ */
static void rt_riscv_stub_announce(const char *name) {
    static const char prefix[] = "STUBBED ";
    for (spl_u64 i = 0; prefix[i] != '\0'; i = i + 1) {
        rt_riscv_uart_put((spl_u64)(spl_u8)prefix[i]);
    }
    if (name) {
        for (spl_u64 i = 0; name[i] != '\0'; i = i + 1) {
            rt_riscv_uart_put((spl_u64)(spl_u8)name[i]);
        }
    }
    rt_riscv_uart_put((spl_u64)'\n');
}

spl_i64 rt_riscv_nvfs_probe(void) {
    rt_riscv_stub_announce("rt_riscv_nvfs_probe");
    return 0;
}

spl_i64 rt_riscv_smf_cli_probe(void) {
    rt_riscv_stub_announce("rt_riscv_smf_cli_probe");
    return 0;
}

spl_i64 rt_riscv_smf_cli_load(void) {
    rt_riscv_stub_announce("rt_riscv_smf_cli_load");
    return 0;
}

spl_i64 rt_riscv_smf_gui_probe(void) {
    rt_riscv_stub_announce("rt_riscv_smf_gui_probe");
    return 0;
}

spl_i64 rt_riscv_native_gui_process_render(void) {
    rt_riscv_stub_announce("rt_riscv_native_gui_process_render");
    return 0;
}

extern spl_i64 desktop_service_entry__spl_start(void) __attribute__((weak));

spl_i64 spl_start(void) __attribute__((weak));
spl_i64 spl_start(void) {
    if (desktop_service_entry__spl_start) {
        return desktop_service_entry__spl_start();
    }
    return 0;
}
