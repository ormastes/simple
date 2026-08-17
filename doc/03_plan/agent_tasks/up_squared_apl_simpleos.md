# UP Squared Apollo Lake SimpleOS handoff

Updated: 2026-08-17
Status: RESUMED — runtime capsule and board-side media transport pending

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
- Partial board-owned entry, console, immutable root, VFS listing, minimal
  linker, and provenance-gated build wrapper are retained in the worktree.

## Current failure evidence

Three bounded build/fix cycles were used. The final build reached the linker
but failed because the minimal entry closure did not link the x86 freestanding
runtime provider (`rt_string_*`, allocation/array/enum helpers,
`serial_println`, and `rt_serial_readline`). Objects were retained at
`.simple/native-objects-Lz0pcQ` when present. Do not repeat the identical
command without changing the runtime-bundle contract.

The 2026-08-17 resume repeated the failure once, then tested explicit
`SIMPLE_NATIVE_BUILD_TARGET` propagation and the documented
`simpleos_x86_64` output discriminator. Both still reached the generic linker
with the same unresolved runtime surface; the last retained objects were under
`.simple/native-objects-Xf8peY`. Both ineffective wrapper experiments were
reverted. The next change must fix or explicitly bind the admitted compiler's
x86 freestanding linker/provider capsule, not retry wrapper naming.

The subsequent 2026-08-17 continuation moved the wrapper to
`x86_64-unknown-simpleos` and built/merged the canonical pure-Simple core plus
freestanding native runtime capsule. That reduced the unresolved surface from
60 symbols to only `rt_serial_readline`. A board-owned bounded COM1 input
provider now exists at
`src/os/kernel/arch/x86_64/up_squared/serial_runtime.c` and is added to that
archive. A new stateful live checker exists at
`scripts/check/check-simpleos-up-squared-apollo-lake.shs`; it is ready for transcript
validation once a writable USB stick and live board boot are available.

The build and checker are now stable for contract/self-test, with USB writer + board
check docs staged for safe handoff.

## External prerequisites still pending

- User selection of feature option A and NFR set A.
- A dedicated removable USB stick or disposable drive in a USB enclosure.
- Live board identity/SKU, CN16 wiring/power, and firmware console-redirection
  evidence.

A passive 115200 8N1 read of Tigard port A captured zero bytes, and neither
current LAN neighbor accepted SSH on port 22. No reset was performed, so this
does not prove a wiring or board failure; it does mean board-side SSH is not
currently an admitted media path.

## Latest admitted artifacts

The next continuation linked successfully after replacing the final missing
conversion with `rt_string_new_literal` and explicitly extracting the proven
x86_64 Multiboot1 CRT. `grub-file --is-x86-multiboot` passes and the ELF entry
is `0x080004e0`.

- ELF: `build/os/up-squared-apollo-lake/simpleos.elf`, 68,936 bytes,
  SHA-256 `0272ea05fec911b115bebc236ebcab8c46065093bde82abc71c4775dfecf3241`.
- USB image: `build/os/up-squared-apollo-lake/usb/board-usb.img`, 256 MiB,
  SHA-256 `03ad0a102eba39d27c9f2ef28939ddd70c667cfaa01388ded628e954ed7f1728`.
- `sgdisk --verify` reports clean primary and backup GPT data; partition 1 is
  EF00 FAT32 and contains a 5,779,456-byte `EFI/BOOT/BOOTX64.EFI`.

The structural checker now uses semantic `sgdisk --verify`, but its historical
`mdir` column parser still rejects the valid spaced 8.3 listing and awaits its
next bounded fix cycle. This does not elevate the image to live hardware PASS.

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

1. Finalize selected requirements; delete the unchosen option documents.
2. Fix the x86 build wrapper by binding the existing freestanding runtime
   bundle/C+ASM providers without fabricated stubs.
3. Add the dedicated catalog/hardening row and focused contract tests.
4. Build the ELF and exact UEFI image; retain compiler/image receipts.
5. Choose physical-move, existing Linux/SSH, or isolated PXE RAM Linux. On the
   actual writer host, admit one stable by-id plus serial/capacity; reject
   root/swap/mounted/internal media; stage+hash, write locally, sync, recheck
   identity, and verify exact-length SHA-256 readback.
6. Use guide: `doc/07_guide/platform/simpleos/up_squared_apl_simpleos.md`.
7. Use F7 for one-time UEFI boot and retain one stateful UART transcript.
8. Inject `ls /`; require output between `ls-begin` and `ls-end` from public
   VFS `readdir`.
9. Update guide, executable/manual SPipe spec, skills, and LLM wiki; verify and
  push the completion change.

## Cooperative ownership

- Sidecar research lanes: completed read-only (repo, hardware, SPipe design).
- Merge owner: primary Codex agent.
- Final reviewer: normal/highest-capability Codex pass after live evidence.
