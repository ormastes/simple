# ARM64 QEMU ivshmem BAR2 mapping blocker

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN, and the cited path is WRONG — recorded so the next lane does not
lose the time this one did.
PATH DRIFT: `grep -n "ivshmem|1af4|0x1110|ECAM|ecam" src/os/kernel/boot/limine_boot_aarch64.spl`
returns **no ivshmem/PCI/ECAM hit at all** (its only match on the pattern set is
:415, an unrelated boot-loop comment). The subject file named by this doc does
not contain the code the doc describes.
Where the ivshmem code actually lives: `grep -rln ivshmem src/os/kernel` returns
exactly two files —
`src/os/kernel/ipc/host_gpu_ivshmem_map.spl` and
`src/os/kernel/arch/x86_64/host_gpu_ivshmem_vmm.spl`.
Note the second is under `arch/x86_64/`. **There is no arm64 ivshmem VMM/ECAM
probe in the tree**, which is a stronger statement than the doc`s "enumeration
returns -2": the arm64 discovery path this doc reports a wrong return code from
does not exist as arm64 code. The doc`s closing TODO (separate discovery vs
BAR-decode causes, raw probe capture) is consequently still entirely unaddressed.
NOT PROVEN: no arm64 QEMU boot was run — bootstrap contention, see the note in
`aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`. Board-run BLOCKED.
