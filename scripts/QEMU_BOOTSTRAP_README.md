# QEMU FreeBSD Bootstrap

This repository now keeps exactly three bootstrap scripts in `scripts/bootstrap/`:

- `bootstrap-from-scratch.sh`
- `bootstrap-from-scratch.bat`
- `bootstrap-from-scratch-qemu_freebsd.sh`

Use `bootstrap-from-scratch-qemu_freebsd.sh` when you want FreeBSD bootstrap inside a QEMU VM.

## Quick Start

```bash
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --step=full2 --deploy
```

The wrapper configures QEMU/SSH/rsync, syncs this repository to the VM, then runs:

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 ...
```

inside the VM.

## Wrapper Options

- `--qemu-vm=PATH` VM image path
- `--qemu-port=N` SSH forward port (default `10022`)
- `--qemu-user=NAME` VM SSH user (default `freebsd`)
- `--skip-sync` skip rsync step
- `--keep-vm-running` do not stop VM after build

All other options are passed through to `bootstrap-from-scratch.sh`.

## Examples

```bash
# Use explicit VM image
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh \
  --qemu-vm=/data/vms/freebsd.qcow2 \
  --step=full2 \
  --deploy

# Fast build without full reproducibility
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --step=full1 --deploy

# Keep VM up for repeated runs
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --keep-vm-running --step=core1
```

## Prerequisites

Host tools:

- `qemu-system-x86_64`
- `ssh`
- `rsync`
- `scp`

VM image auto-detection paths:

- `build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2`
- `~/.qemu/freebsd.qcow2`
- `/opt/qemu/freebsd.qcow2`

If no image is detected, pass `--qemu-vm=PATH`.

## Output

On success, the wrapper retrieves and deploys:

- `bin/release/simple`

from the VM to the host workspace.
