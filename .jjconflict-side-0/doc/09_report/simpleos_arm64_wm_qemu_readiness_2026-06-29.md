# SimpleOS ARM64 WM QEMU Readiness Evidence

Date: 2026-06-29

## Status

- arm64_wm_qemu_readiness: ready
- qemu_system: qemu-system-aarch64
- qemu_path: /usr/bin/qemu-system-aarch64
- machine_virt: true
- ramfb_device: true
- dry_run_parse: true
- host_os: Linux
- host_machine: x86_64
- accelerator: tcg
- cpu: cortex-a57
- entry: examples/09_embedded/simple_os/arch/arm64/wm_entry.spl
- io: examples/09_embedded/simple_os/arch/arm64/wm_entry_io.spl
- guide: doc/07_guide/platform/simpleos/simpleos_arm64_wm_qemu.md

## Command

```bash
sh scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs
```

The readiness probe verifies QEMU command availability, `virt` machine support,
`ramfb` device support, and host-appropriate dry-run parsing. It is not a live
ARM64 WM boot proof; serial markers remain the boot acceptance gate.
