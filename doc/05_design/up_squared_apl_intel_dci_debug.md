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
does not consume `DciStorageWrite` image-write admission because this operation
formats a named filesystem rather than copying an external disk image; both
paths preserve the same no-debugger-MMIO boundary.

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
execution transition.

## Missing UEFI adapter

No current executable consumes `DciMailboxDescriptor`. The required adapter
must still reserve/publish storage through UEFI boot services, generate a
per-boot nonce, snapshot the descriptor twice around SHA-256, apply the admitted
ELF plan, obtain the final memory map, retry `ExitBootServices` only for a stale
map key, park APs, and invoke the reviewed shim. Until that code and an OVMF
producer/consumer test exist, the mailbox layer is policy evidence only.

The implementation must replace the mailbox portion of the GRUB-first topology,
not patch the later ELF32 shim and call it UEFI-resident. The required capsule
is a PE32+ EFI application with the firmware's Microsoft x64 calling convention.
It reserves the descriptor, payload, destination, stack, and transition pages
before publishing their addresses; after stable double-snapshot and SHA-256/ELF
admission it obtains the final memory map, performs the bounded
`ExitBootServices` retry, and enters a reviewed 64-to-32-bit transition that
supplies the Multiboot2 magic and information pointer. The existing GRUB image
remains the fallback first-boot path until that capsule passes OVMF.
