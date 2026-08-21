<!-- codex-design -->
# Architecture: UP Squared Apollo Lake Intel DCI debug and provisioning

## Decision

Use a transport-neutral, pure-Simple admission capsule between Intel DCI and all
target mutation. Intel tooling may transport bytes or control execution, but it
never owns ELF interpretation, memory policy, boot-state construction, or block
I/O. Those decisions remain target-side and independently testable.

## Layers

1. **Connection owner:** Intel System Debugger/Target Connection Agent. It emits
   a retained identity receipt; no repository code reimplements proprietary DCI.
2. **Mailbox protocol owner:** `up_squared/dci_mailbox.spl` validates schema,
   generation, nonce, commit state, payload length, and SHA-256.
3. **Load-plan owner:** the same pure capsule parses x86-64 ELF `PT_LOAD`
   metadata, enforces file/physical bounds and non-overlap, and requires the
   entry to lie in an executable segment inside one allowed UEFI RAM range.
4. **UEFI adapter:** `up2_dci_uefi_loader.c` is a directly entered GNU-EFI
   PE32+ application. It reserves all fixed ranges before publication,
   authenticates wire-v1, validates/copies the ELF64 segments, builds the final
   UEFI memory-map tag, exits boot services, and calls
   `up2_dci_uefi_transition.S`, which enters the embedded existing Multiboot2
   ELF32 shim. OVMF exercises this with one CPU; physical-UP2 MP topology and
   the PI ExitBootServices AP-idle contract remain an open board evidence gate.
5. **Storage-policy owner:** pure Simple admits one observed device and bounded
   write request. The implemented UP2 NVMe adapter uses the common controller,
   lease-backed block adapter, GPT, and FAT32 owners for write/flush/fresh-
   adapter readback; debugger MMIO is never a storage backend. Physical-board
   evidence remains separate from the passed QEMU scratch-device proof.
   Raw-image I/O is owned by host-neutral
   `os.services.storage_image_provision`: it depends only on `BlockDevice` and
   constant-memory streaming SHA-256 and owns alignment, ordered chunk writes,
   flush, and exact full readback. UP2 owns PCI/Identify identity, confirmation, staging-memory
   copy, and fresh NVMe adapters; StarFive can reuse the common owner without
   copying its JH7110 PCIe/PHY/cache-coherency port.
6. **Evidence owner:** connection, load, boot, and storage receipts remain
   separate and cannot promote one another.
7. **Free post-boot monitor:** `gdb_rsp_monitor.spl` owns packet, checksum,
   bounds, and readback policy. `gdb_rsp_uart.spl` alone owns CN16/COM1 framing.
   The linker reserves `0x0a000000..0x0b000000` in the admitted writable
   `PT_LOAD`; the monitor cannot address outside it. High-volume `M` packets
   use scalar parsing directly into staging; generic packets retain text framing.

## Pattern evaluation

- **Selected: capability adapter + virtual capsule.** Proprietary transport and
  hardware actions are injected capabilities; protocol/policy stays portable.
- **Rejected: debugger script as bootloader.** It couples NDA APIs to CPU state
  and cannot safely own UEFI memory, AP state, or Multiboot construction.
- **Rejected: direct DCI storage MMIO.** It bypasses driver ordering, flush, and
  identity checks.
- **Deferred: xHCI DbC.** It is a different post-entry transport and was not
  selected.
- **Selected free fallback: bounded GDB RSP memory access.** It supplies
  post-boot staging without claiming DCI preboot halt, registers, breakpoints,
  reset, or CPU-state boot.

## Trust boundaries

The descriptor is untrusted until its final committed state validates. Payload
bytes are untrusted until exact SHA-256 and ELF checks pass. UEFI memory-map
ranges are authoritative only for the current boot generation. Storage identity
is re-read before and after write. Integer arithmetic uses subtraction-based
bounds tests to avoid wraparound.

Streaming SHA owns one preallocated 64-byte block and 64-word schedule and
mutates its eight state words in place. Per-block allocation and large-array
reads at changing offsets are outside the freestanding monotonic-heap contract.

## Reset

Apollo Lake OpenRC warm reset is architecturally forbidden because Intel
documents an undefined-state stranded-core failure. The baseline recovery
capability is physical reset; Power-Good reset is a separately qualified adapter.

## Completion boundary

Host-independent protocol and OVMF tests do not prove physical DCI, physical
boot, or storage writes. Hardware PASS requires the exact receipts in REQ-003,
REQ-010, and REQ-011.
OVMF may independently prove REQ-013 packet write/readback behavior; physical
CN16 still requires a fresh board transcript.
The pure mailbox capsule alone is not boot evidence. The separate PE32+ adapter
is now `EFI/BOOT/BOOTX64.EFI`; GRUB moved to `EFI/BOOT/GRUBX64.EFI` and is
chainloaded only after an uncommitted timeout. The adapter is C/assembly because
the current Simple target matrix does not expose the UEFI Microsoft x64 ABI or
COFF application boundary. Its embedded ELF32 shim remains the independent
post-UEFI ELF loader. The OVMF receipt proves this software topology, while a
physical DCI receipt and firmware/kernel AP-state evidence are still required
for the multi-core board claim.
