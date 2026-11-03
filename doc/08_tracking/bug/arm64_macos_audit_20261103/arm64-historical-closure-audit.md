# ARM64 historical closure source audit — 2026-11-03

Baseline: `a41511004a0`, read-only inspection. No build, QEMU, regression, or DB mutation. Recommendations distinguish a visible incomplete source path from a newly reproduced native failure.

## ARM64 ivshmem: recommend P2 open

`host_gpu_ivshmem_map.spl:1` imports `os.drivers.pci.pci`. Its discovery calls `pci_read_vendor`, and its BAR programming calls `pci_write_config`. The actual owner `src/os/drivers/pci/pci.spl:60` reads through x86 port I/O, while ARM64 writes at line 90 derive the MMIO address from `_pci_ecam_base()` returning zero (line 86). The x86 adapter directly re-exports the x86 port owner; it does not select ARM64 ECAM. This is concrete current source evidence of an unwired non-x86 PCI route, not merely an old report.

Commit `3be7662046a45b64099ff9f92495153e6b25a340` (2026-10-16), “declare never-existing _pci_ecam_base legacy stub,” explicitly says the read path never existed and the owner must wire a `PciHostDescriptor` from platform DTB or delete legacy shims. It only restored resolver compilation; it did not repair hardware access. The mapper now separates discovery reasons (-71/-6/-2), partly satisfying the historical diagnostic TODO. No native enumeration/BAR acceptance receipt was found. Correct the registry owner from `limine_boot_aarch64.spl` to the PCI/map path. Do not claim the historical exact -2 was freshly reproduced.

## LLD defsym: open diagnostic triage, not confirmed recurrence

`simpleos_native_symbols.spl:159` returns the exact nm-discovered `__spl_start` suffix symbol. `simpleos_native_linkers.spl:100,107,539` interpolates it directly into the defsym expression; no expression-level quoting is applied. Blame identifies `b81cd5afd72c` (2026-08-22, multiarch execution/toolchains) for the ARM64 line, not a quoting repair.

However, the original report mixed source/entry roots and explicitly requires a correctly rooted reproduction. Source inspection cannot establish that current canonical compilation still generates punctuation-bearing names. No bounded history evidence explained the closure. Recommend explicit `open` diagnostic triage with “current correctly rooted reproducer unverified”; do not call it source-fixed, reproduce-by-inspection, or silently patch the symbol. If registry policy requires fresh execution before reopening, retain historical status with this unresolved acceptance annotation until the focused producer check is allowed.

## RV64 exit facade: preserve scoped closure

`examples/09_embedded/simple_os/arch/riscv64/host_gpu_smoke_entry.spl:2,6` imports/calls `sbi_shutdown`, matching the report's scoped RV64 resolution. Blame reaches restoration commit `ae55a7467197`; it does not identify the original fix. ARM64 smoke/Vulkan entries still call `rt_qemu_exit_success`, but ARM64 `boot/baremetal_stubs.c:2376` contains a real PSCI SYSTEM_OFF/semihosting exit implementation. This is an architecture-facade ownership follow-up, not proof of a missing/fake exit. Preserve RV64 closure; track ARM64 facade migration separately if still required.

Bounded registry history reached restoration/transplant commits (`cf999f85841`, `88aac2ffe28`, `bb3f6ab8ab2`), not an independently supported closure decision. These must not be cited as native repair evidence.

## Accepted independent-review disposition

Reopen ARM64 ivshmem only, based on the independently confirmed current unwired PCI/zero-ECAM source path. Retain LLD and RV64 historical closure; LLD current correctly rooted trigger remains unverified and is tracked as an acceptance/triage followup. No fresh native recurrence is claimed.
