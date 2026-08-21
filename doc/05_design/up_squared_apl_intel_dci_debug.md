<!-- codex-design -->
# Detail design: UP Squared Apollo Lake DCI mailbox and provisioner

## Pure-Simple interfaces

`src/os/kernel/arch/x86_64/up_squared/dci_mailbox.spl` owns:

- `DciCommitState`: `Empty`, `PayloadWritten`, `Committed`.
- `DciMailboxDescriptor`: schema, generation, nonce, payload size/hash/state.
- `DciMemoryRange`: allowlisted physical start and size.
- `DciLoadSegment`: file offset/size, physical address/memory size, flags.
- `DciStorageIdentity`: model, serial, transport, capacity, and safety state.
- `DciStorageWrite`: observed/expected identity, bounds, image hash/size, and
  confirmation challenge.
- `DciAdmission`: exact `accepted` boolean and stable reason string.

Public functions:

- `dci_admit_mailbox(...)`: validates final commit, replay resistance, exact
  length, digest syntax, and independently observed SHA-256.
- `dci_parse_x86_64_elf(bytes)`: parses physical `p_paddr`, unlike
  the process-loader's virtual-only plan.
- `dci_admit_load_plan(...)`: validates segment/file/memory arithmetic,
  allowlist containment, pairwise non-overlap, W^X, and executable entry.
- `dci_storage_confirmation(...)`: binds device identity, capacity, byte range,
  and image hash.
- `dci_admit_storage_write(...)`: rejects ambiguity, system/mounted/held media,
  identity mismatch, bad bounds, bad hash, or wrong challenge.

## Mailbox ordering

The producer clears commit state, writes payload, writes the non-commit
descriptor fields, then writes `Committed` last. The consumer snapshots the
descriptor twice around hashing; both snapshots must match in the future UEFI
adapter. Pure admission receives the stable snapshot and observed digest.

## Load algorithm

1. Validate ELF64 little-endian, `ET_EXEC`, `EM_X86_64`, header sizes, program
   table bounds, and at least one `PT_LOAD`.
2. Preserve `p_offset`, `p_paddr`, `p_filesz`, `p_memsz`, flags, and alignment.
3. Reject overflow, truncation, `filesz > memsz`, zero memory size, more than 64
   segments, overlap, non-allowlisted physical memory, or W+X.
4. Require entry inside a loadable executable segment.
5. The UEFI adapter copies `filesz`, zeros the remainder, flushes instruction
   visibility as needed, and invokes the established shim.

## Storage algorithm

The hardware adapter enumerates one candidate and creates immutable observed
identity. Policy compares it with operator expectation and rejects root, swap,
mount, holder, non-persistent authorization, zero length, range overflow, or
image-length mismatch. The adapter re-enumerates before write, writes exact
bounds, flushes, re-enumerates again, and hashes exact readback.

The landed UP2 NVMe provisioner is the first concrete hardware adapter. Boot
performs PCI grant plus Identify only. `nvme format <exact live challenge>`
creates mirrored GPT and a FAT32 partition lease, writes `PROOF.TXT`, flushes,
constructs a fresh adapter, and verifies bytes before `ls /nvme` succeeds. It
remains the named-filesystem path.

The raw-image path is separate and consumes `DciStorageWrite`. The UP2 leaf
captures immutable Identify/PCI identity and an exact plan, prints the full
identity plus a line-bounded confirmation containing SHA-256 of its canonical
model/serial/transport/capacity, and copies at most 1 MiB from the 16 MiB RSP staging window per
ordered command. `os.services.storage_image_provision` is host-neutral: it
validates sector geometry/range, verifies each chunk hash before writing,
flushes, and computes streaming whole-image SHA-256 over every sector from a
fresh adapter. Any device/admission/write error aborts the session; restart
requires a new plan and confirmation. The same common owner is available to a
future StarFive adapter without copying PCIe/PHY/cache-coherency logic.

The UP2 leaf retains long-lived plan/session/expected-identity state only in
module-owned scalar and text globals. Transient value-semantic plans cross into
the shared owner for one call; no aggregate survives through an optional global.

`Sha256Stream` owns one preallocated block and schedule for its lifetime. Update
copies input bytes into that block, processes full blocks in place, and never
returns aggregate state per block. This keeps target hashing bounded on the
16 MiB monotonic freestanding heap.

## Error behavior

All validation returns a stable reason. No validation function writes memory,
registers, firmware, or storage. Hardware adapters must stop before mutation on
any rejected admission.

## Free GDB RSP memory monitor

`gdb_rsp_monitor.spl` parses checksummed printable-ASCII packets independently
of transport. It supports `qSupported`, attachment/thread discovery, `H`, `?`,
detach, and bounded `m`/`M`; all register, breakpoint, continue, step, and reset
packets return unsupported. Each request is limited to 1024 bytes and to the
16 MiB linker-owned staging range `0x0a000000..0x0b000000`. `M` reads every
written byte back before replying `OK`.

`gdb_rsp_uart.spl` enters only after the shell command `gdb`, ACKs valid frames,
NACKs malformed/checksum-failed frames, handles Ctrl-C as an already-stopped
monitor indication, and returns to the shell on detach. It performs no reset or
execution transition. Frame assembly uses one append-only byte array and one
final bytes-to-text conversion; per-character text concatenation is forbidden
because the freestanding 16 MiB monotonic heap cannot reclaim those copies.

## UEFI adapter

`up2_dci_uefi_loader.c` implements the PE32+ firmware boundary with GNU-EFI.
Before publishing it reserves the 128-byte mailbox page, 16 MiB payload window,
48 MiB kernel window, 256 KiB Multiboot-info/map window, and 64 KiB embedded-shim
window. The host writes payload, non-commit descriptor bytes, then the aligned
32-bit commit word. The consumer requires the published nonce and fixed ranges,
stable snapshots around two payload hashes, zero reserved/control fields, exact
SHA-256, bounded non-overlapping ELF64 load segments, and an executable entry.
The nonce comes from UEFI RNG or hardware RDRAND. Time/TSC is labeled
diagnostic-only, and a committed request with only that weak fallback is denied.

The final memory-map call writes an EFI memory-map Multiboot2 tag beside a
module tag for the staged kernel. `ExitBootServices` retries once only for a
stale key. `up2_dci_uefi_transition.S` disables paging and long mode in the
architected order and enters the embedded existing ELF32 shim with Multiboot2
magic and information pointer. The shim independently reloads the module and
enters the kernel `_entry32`. An uncommitted ten-second timeout chainloads
`GRUBX64.EFI`; committed invalid input fails closed. `--ovmf-dci-admission`
proves the full RAM-authored boot with `-smp 1`; physical multi-core AP state is
not inferred. PI firmware owns the ExitBootServices AP-idle transition;
physical evidence must bind firmware MP topology and later kernel AP policy.
