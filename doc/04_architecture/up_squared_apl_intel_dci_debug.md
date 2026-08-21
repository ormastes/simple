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
4. **UEFI adapter:** a future board capability supplies the current memory map,
   reserves the mailbox/load ranges, performs copy/zero, exits boot services,
   parks APs, and invokes the existing Multiboot2 shim.
5. **Storage-policy owner:** pure Simple admits one observed device and bounded
   write request. A separate board storage capability performs write/flush/
   readback; debugger MMIO is never a storage backend.
6. **Evidence owner:** connection, load, boot, and storage receipts remain
   separate and cannot promote one another.
7. **Free post-boot monitor:** `gdb_rsp_monitor.spl` owns packet, checksum,
   bounds, and readback policy. `gdb_rsp_uart.spl` alone owns CN16/COM1 framing.
   The linker reserves `0x0a000000..0x0b000000` in the admitted writable
   `PT_LOAD`; the monitor cannot address outside it.

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
