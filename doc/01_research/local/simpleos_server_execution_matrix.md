# Local research: SimpleOS server execution matrix

## Existing owners

- `src/os/kernel/net/rt_net_socket_facade.spl` is the canonical SimpleOS
  socket facade and already backs x86/RISC-V HTTP/DB services.
- `src/os/kernel/boot/http_baremetal.spl` and `src/os/apps/dbd/dbd.spl` contain
  bounded HTTP and database service behavior; platform work must expose I/O,
  not duplicate these protocols.
- `src/os/userlib/{fs,net}.spl` and `src/os/userlib/syscall_raw.spl` define the
  mounted-executable syscall surface.
- ARM64 currently routes mounted ELFs through
  `examples/09_embedded/simple_os/arch/arm64/boot/crt0.S` and
  `baremetal_stubs.c`; that bridge lacks the selected file/network syscall
  implementation and contains stubbed `rt_net_*` symbols.
- `src/os/port/qrb2210_*` contains typed physical display/input/audio/Vulkan
  owner contracts, but the connected board has no deployed SimpleOS provider.
- Existing x86 combined server and ARM filesystem-exec gates are useful
  components but neither proves an ARM filesystem-launched server.

## Reuse decision

Implement transport and syscall mechanisms at their ARM/kernel owners, reuse
the existing HTTP/DB protocol owners, and keep VFS/loader provenance. For UNO Q,
reuse the QRB2210 typed device contracts and add packaging/boot/runtime evidence
rather than running a Debian process and relabeling it.

## 2026-08-14 QRB2210 boot/download owner audit

The repository has no QRB2210 owner for a boot manifest, signed Qualcomm boot
chain inputs, partition map, EDL/download transaction, rollback/recovery, or a
SimpleOS rootfs carrier. The existing `qrb2210_*` modules begin at physical
display/input/audio/Vulkan admission, and the live runner begins from ADB on the
vendor Debian installation. Neither boundary can install or prove SimpleOS.

The safe implementation boundary is therefore a new platform-owned image and
boot-admission lane, not an extension of the Debian/ADB evidence runner. It must
consume vendor-authorized signed boot-chain artifacts and a board/revision-
matched partition manifest, preserve a verified factory recovery image, and
make download mutation opt-in behind the board lock. No source-only owner can
truthfully invent Qualcomm signatures, partition names, or an Arduino-supported
custom-OS recovery procedure, so implementation remains blocked on those
authoritative inputs.
