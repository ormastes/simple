# ARM64 QEMU ivshmem BAR2 mapping blocker
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

A manually replayed link using the compiler-produced objects plus the existing
ARM CRT/runtime creates a valid static AArch64 ELF at `0x40000000`, with zero
undefined symbols and an exact `spl_start` alias.

With explicit `-display none -monitor none -serial stdio`, QEMU boots that ELF
through CRT, runtime, PCI scan, and `spl_start`. The backend object alone
correctly leaves two PCI devices; attaching ivshmem adds bus-0 device `1af4:1110`
at `00:02.0` and still reaches the probe. QEMU reports BAR2 as 64-bit,
prefetchable, and 8 MiB; ECAM reads `BAR2=0x0000000c`, `BAR3=0`.

After reason separation, the guest returns `-2` (scan exhaustion) even though
QEMU exposes `1af4:1110`. Removing class/subclass from the matcher and rebuilding
from a fresh cache does not change the result, so that ineffective change was
reverted. The mismatch occurs earlier in the Simple ECAM read/enumeration path.
`highmem=off` causes an unrelated early fault and is rejected as a workaround.

TODO: give discovery and BAR decode distinct stable reasons, capture raw/probe
low/high values through the existing serial evidence path, and fix the PCI
config write/probe owner. The intended BAR window `0x3e000000..0x3e7fffff` is
inside low PCI MMIO and does not overlap ECAM or the ELF. Do not bypass BAR
discovery or add a guest success marker.


## 2026-11-03 source review and raw firmware handoff prerequisite

The current Simple PCI read owner still selects x86 CF8/CFC port I/O;
its ARM64 write override obtains an ECAM base of zero. The shared
`PciHostDescriptor` and checked address helper exist, but the active ARM64
Linux Image entry discarded firmware x0 before entering Simple code.

The startup prerequisite now retains x0 in reserved boot register x20 across
relocation and publishes it only after clearing BSS. The exported
`rt_arm64_boot_dtb_address()` returns that **untrusted raw scalar**, with zero
meaning absent. It does not dereference firmware bytes, validate the DTB,
protect its bytes from kernel/scratch/BSS overlap, or initialize PCI.

A lightweight ARM64 user-emulation fixture checks the exact publication/getter
with both direct and relocated startup shapes; missing-save and
publish-before-BSS-clear mutations must fail. Cross-assembly checks the full
production startup object. These tests do not execute privileged EL/MMU/cache
transitions, full firmware boot, or a PCI device.

The bug remains OPEN. A checked boot-memory range owner, PCI `reg`/`bus-range`/
`ranges` decoder using the shared FDT reader, and descriptor-backed ECAM/BAR
access are still required before native ivshmem discovery can be verified.
No hardcoded ECAM address, synthetic vendor ID, or zero-base fallback is an
acceptable substitute. The current self-relocation direction and possible
DTB-byte overlap are separate boot constraints; saving x0 does not fix them.
