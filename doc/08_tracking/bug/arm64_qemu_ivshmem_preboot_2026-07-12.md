# ARM64 QEMU ivshmem BAR2 mapping blocker

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
