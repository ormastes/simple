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

1. Finalize selected requirements; delete the unchosen option documents.
2. Fix the x86 build wrapper by binding the existing freestanding runtime
   bundle/C+ASM providers without fabricated stubs.
3. Add the dedicated catalog/hardening row and focused contract tests.
4. Build the ELF and exact UEFI image; retain compiler/image receipts.
5. Choose physical-move, existing Linux/SSH, or isolated PXE RAM Linux. On the
   actual writer host, admit one stable by-id plus serial/capacity; reject
   root/swap/mounted/internal media; stage+hash, write locally, sync, recheck
   identity, and verify exact-length SHA-256 readback.
6. Use F7 for one-time UEFI boot and retain one stateful UART transcript.
7. Inject `ls /`; require output between `ls-begin` and `ls-end` from public
   VFS `readdir`.
8. Update guide, executable/manual SPipe spec, skills, and LLM wiki; verify and
   push the completion change.

## Cooperative ownership

- Sidecar research lanes: completed read-only (repo, hardware, SPipe design).
- Merge owner: primary Codex agent.
- Final reviewer: normal/highest-capability Codex pass after live evidence.
