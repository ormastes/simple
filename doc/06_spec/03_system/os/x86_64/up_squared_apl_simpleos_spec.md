# SimpleOS on UP Squared Apollo Lake

Source: `test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl`

First run the contract and negative policy checks. These do not claim a board
boot:

```sh
scripts/check/check-simpleos-up-squared-apollo-lake.shs --contract
scripts/check/check-simpleos-up-squared-apollo-lake.shs --self-test
```

Build the admitted kernel and image, then move the USB stick to a writer host.
The offline contract verifies the ELF64 Multiboot2 header and embedded GRUB
command. Before writing media, run the exact-image firmware preflight:

```sh
scripts/check/check-simpleos-up-squared-apollo-lake.shs --ovmf
```

It must reach the ELF32 shim, 64-bit kernel, ordered markers, and a fresh
VFS-backed `ls /`. This is an offline preflight, not physical-board evidence.
Run `write-simpleos-up-squared-usb.shs` without `--write-media` to obtain the
identity-bound challenge. After verifying model, serial, and capacity, rerun as
root with `--write-media` and that exact confirmation. Retain its receipt.

Insert the stick into a UP2 Type-A host port, use F7 for the one-time UEFI
choice, connect CN16 as 3.3 V TTL, and run:

```sh
UP2_MEDIA_RECEIPT=/absolute/path/to/media.receipt \
  scripts/check/check-simpleos-up-squared-apollo-lake.shs --live
```

PASS requires ordered physical boot markers followed by a freshly transmitted
`ls /` whose VFS-correlated window contains `/bin`, `/etc`, and `/README.txt`.
Missing board/UART evidence is BLOCKED; offline artifacts never substitute.
