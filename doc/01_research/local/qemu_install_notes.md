# QEMU Install Notes

TLS 1.3 integration tests and any SimpleOS QEMU-based test require
`qemu-system-x86_64`. The test harness gracefully skips and produces a
degraded report when the binary is absent, but contributors who want full
green runs need it installed locally. This doc records install paths for
common dev environments.

## Install commands

### Debian / Ubuntu

```bash
sudo apt install qemu-system-x86
```

### Fedora / RHEL

```bash
sudo dnf install qemu-system-x86
```

### Arch Linux

```bash
sudo pacman -S qemu-system-x86
```

### macOS (Homebrew)

```bash
brew install qemu
```

## Verification

```bash
qemu-system-x86_64 --version
# should print: QEMU emulator version 8.x or newer
```

## Minimum version

The test scripts (`scripts/os_qemu_test.shs`, `scripts/os_gui.shs`) pass
`-machine q35`, which requires QEMU 2.4 or newer. Current Ubuntu LTS and
Homebrew ship QEMU 8.x, well above this floor. No other version-sensitive
flags (`-device virtio-gpu-pci`, `-device virtio-net`, etc.) were found in
the harness — stick with whatever the distro package manager provides unless
you are debugging a specific hardware-model issue.

## Test specs that require QEMU

Once `qemu-system-x86_64` is installed, the following specs will run in full
rather than skip to a degraded report:

| Spec | Purpose |
|------|---------|
| `test/system/os_tls_system_spec.spl` | TLS 1.3 integration vs rustls |
| `test/system/os_tls_spec.spl` | TLS 1.3 unit in QEMU |
| `test/system/os_full_stack_spec.spl` | Full OS stack smoke test |
| `test/system/os_network_spec.spl` | Network stack |
| `test/system/os_shell_spec.spl` | Shell in SimpleOS |
| `test/system/os_storage_spec.spl` | Storage / FAT32 |
| `test/system/os_boot_integration_spec.spl` | Boot integration |
| `test/system/os_compiler_bootstrap_spec.spl` | Compiler bootstrap in OS |
| `test/system/os_ssh_spec.spl` | SSH inside OS |
| `test/system/os_crypto_spec.spl` | Crypto primitives |
| `test/system/os_desktop_integration_spec.spl` | Desktop / GUI integration |

## Related docs

- General baremetal / QEMU backend setup (ARM, RISC-V, x86):
  `doc/07_guide/backend/baremetal.md`
- Platform-specific VM setup (FreeBSD, etc.):
  `doc/07_guide/platform/platforms.md`
- Dev-tool bootstrap (does not install QEMU; add it separately):
  `scripts/install-dev-tools.sh`
