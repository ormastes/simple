# Feature requirement options: SimpleOS on UP Squared Apollo Lake

Status: pending user selection

## Option A — Removable UEFI USB first light (recommended)

Build a dedicated UP2 x86_64 kernel and GPT/FAT32 image, write only to one
explicitly admitted removable USB identity, choose it once with F7, capture
UART, and prove interactive VFS-backed `ls /`.

- Pros: non-destructive to the board; uses standard UEFI fallback; easiest to
  recover and reproduce; matches existing repository tooling.
- Cons: requires a separate removable USB stick and physical F7/power action;
  firmware serial redirection may need setup.
- Effort: medium.

## Option B — Network/PXE boot

Serve the image over PXE and boot it from the firmware network menu.

- Pros: no removable media writes; fast later iteration.
- Cons: requires a configured network link/DHCP/TFTP and proven UP2 PXE ROM;
  current host exposes no UP2 network interface and SimpleOS physical NIC
  support is not yet established.
- Effort: high.

## Option C — Install to onboard eMMC

Write a bootable image or EFI files to the UP2 internal eMMC.

- Pros: standalone boot after installation.
- Cons: destructive/recovery risk; may overwrite the installed OS or boot
  records; unnecessary for first light.
- Effort: high.

Selection required before final requirements and implementation are frozen.
