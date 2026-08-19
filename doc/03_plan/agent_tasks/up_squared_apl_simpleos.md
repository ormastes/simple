# UP Squared Apollo Lake SimpleOS handoff

Updated: 2026-08-17
Status: IMPLEMENTED OFFLINE — physical media write, boot, and UART proof pending

## Objective retained

Create `x86_64-up-squared-apollo-lake`, build a safe removable UEFI image,
boot the physical board, and prove command-correlated VFS `ls /` over UART.
This lane is not complete and must not be reported as a physical-board PASS.

## Completed research and preparation

- Local/domain research and feature/NFR option documents exist.
- Recommended path is removable GPT/FAT32 UEFI USB selected once with F7.
- CN16 contract is 3.3 V TTL, initially 115200 8N1; live firmware output is
  not yet observed.
- CN22 is CPLD/BIOS-update JTAG at 1.8 V, not a documented Apollo Lake CPU
  debug port. Never drive it for SimpleOS debugging.
- `mtools` was installed on the Linux host.
- Board-owned entry, console, immutable root, VFS listing, linker, and
  provenance-gated build wrapper produce an admitted x86_64 ELF.
- The exact-kernel UEFI image wrapper, fail-closed stable-by-id removable-media
  writer, one-session live UART checker, architecture/detail design, test plan,
  executable SSpec, and manual are implemented.

## Current evidence

The runtime blocker is closed: the wrapper now binds the admitted simple-core
archive, native runtime members, board serial provider, and Multiboot crt0.
The resulting x86_64 ELF and GPT/FAT32 UEFI image pass their offline checks.
Physical completion still requires an admitted removable-media receipt and a
fresh UP2 UART transcript; retained historical logs are not accepted.
The OVMF preflight now proves USB discovery, standalone GRUB startup, and
Multiboot2 ELF admission, but `boot` does not reach `_entry32`; see
`doc/08_tracking/bug/up2_grub_multiboot2_transition_2026-08-20.md`.

## External prerequisites still pending

- User selection of feature option A and NFR set A.
- A dedicated removable USB stick or disposable drive in a USB enclosure.
- Live board identity/SKU, CN16 wiring/power, and firmware console-redirection
  evidence.

On the 2026-08-17 resume, Linux enumerated only the internal system NVMe and a
USB `Smart KM Link` read-only optical-class device (`sr0`). No removable USB
mass-storage disk or stable USB disk by-id path was present. Never reinterpret
that `sr0` device or the host NVMe as the requested install target. If the stick
was inserted into the UP2 rather than this build host, move it to the build
host for image installation, then return it to the UP2 for F7 boot. If that is
impractical, first prove UP2 boots trusted Linux/SSH from other media, or PXE a
RAM Linux environment on an isolated network; only then use a board-local
identity-gated writer. Do not infer remote access from Micro-B OTG or UART.

## Resume sequence

1. Add the dedicated catalog/hardening row and focused contract tests.
2. Build the ELF and exact UEFI image; retain compiler/image receipts.
3. Choose physical-move, existing Linux/SSH, or isolated PXE RAM Linux. On the
   actual writer host, admit one stable by-id plus serial/capacity; reject
   root/swap/mounted/internal media; stage+hash, write locally, sync, recheck
   identity, and verify exact-length SHA-256 readback.
4. Use F7 for one-time UEFI boot and retain one stateful UART transcript.
5. Inject `ls /`; require output between `ls-begin` and `ls-end` from public
   VFS `readdir`.
6. Verify and push the completion evidence change.

## Cooperative ownership

- Sidecar research lanes: completed read-only (repo, hardware, SPipe design).
- Merge owner: primary Codex agent.
- Final reviewer: normal/highest-capability Codex pass after live evidence.
