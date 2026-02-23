# QEMU FreeBSD Bootstrap Guide

Use the dedicated wrapper script:

- `scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh`

This wrapper configures a FreeBSD QEMU VM environment, then invokes:

- `scripts/bootstrap/bootstrap-from-scratch.sh`

inside the VM.

## Quick Start

```bash
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --step=full2 --deploy
```

## Common Commands

```bash
# Custom VM image and port
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh \
  --qemu-vm=/path/to/freebsd.qcow2 \
  --qemu-port=10023 \
  --step=full2 \
  --deploy

# Fast development run (skip full2)
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --step=full1 --deploy

# Keep VM running for repeated builds
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --keep-vm-running --step=core1
```

## Wrapper Options

| Option | Description | Default |
|--------|-------------|---------|
| `--qemu-vm=PATH` | FreeBSD qcow2 image path | Auto-detect |
| `--qemu-port=N` | SSH forwarded host port | `10022` |
| `--qemu-user=NAME` | SSH user inside VM | `freebsd` |
| `--skip-sync` | Skip rsync to VM | Off |
| `--keep-vm-running` | Keep VM running after build | Off |

All other arguments are forwarded to `bootstrap-from-scratch.sh` in the VM.

## Prerequisites

Install host tools:

```bash
# Debian/Ubuntu
sudo apt-get install -y qemu-system-x86 openssh-client rsync
```

VM image is auto-detected from:

- `build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2`
- `~/.qemu/freebsd.qcow2`
- `/opt/qemu/freebsd.qcow2`

If needed, pass `--qemu-vm=/path/to/image.qcow2`.

## Output

After success, host workspace contains:

- `bin/release/simple`

## Troubleshooting

- VM image not found: pass `--qemu-vm=PATH`
- SSH timeout: verify VM can boot and port forwarding is free
- rsync/scp not found: install `rsync` and OpenSSH client tools
