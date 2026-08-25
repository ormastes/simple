# Cosmos FSBL C / Pure-Simple coverage parity — 2026-08-25

## Scope and result

This host lane covers the six-input FSBL handoff decision used by the
Cosmos+ Zynq-7000 silicon profile.  It does not claim ARM32 firmware linkage:
`doc/08_tracking/bug/pure_simple_arm32_emit_object_ignored_2026-08-24.md`
remains open, so the Pure-Simple compiler cannot yet provide the relocatable
ARM object required by the firmware link.

The C oracle and Pure-Simple decision core use the same seven vectors.  One
valid vector establishes the baseline; six further vectors independently
toggle SLCR lock, ARM clock, DDR clock, PS primary reset, A9 CPU0 reset, and
DEVCFG PCFG_DONE.  Every atomic condition is therefore shown to affect the
result independently (6/6 MC/DC conditions, 100%).  Expected results are one
valid handoff and six fail-closed handoffs.

## Measured C branch evidence

GCC `--coverage -O0`, `gcov -b -c`, the silicon/mock-MMIO profile, and the
normal-process-per-case runner were used before and after the vector change.
The source under measurement was
`src/os/kernel/arch/arm32/cosmos/cosmos_fsbl.c`.

| Measurement | Branches executed | Arcs taken at least once |
| --- | ---: | ---: |
| Before | 75.00% (12/16) | 50.00% (8/16) |
| After, raw gcov denominator | 100.00% (16/16) | 87.50% (14/16) |
| After, host-executable decision denominator | 100.00% (14/14) | 100.00% (14/14) |

The two raw arcs not taken are the deliberately failing returns inside
`cosmos_fsbl_selftest`: one would require the all-good register tuple to be
rejected, and the other would require the missing-PCFG tuple to be accepted.
They cannot be activated through inputs without breaking the helper being
self-tested.  The test executes both decisions and their required success
outcomes; they are excluded only from the input-reachable denominator, not
reported as covered.

The `COSMOS_IS_QEMU` compile-time `COSMOS_UNAVAILABLE` branch is a distinct
target configuration and is absent from this silicon-profile gcov binary.
Physical BootROM/FSBL handoff and PL hardware behavior likewise require the
target and remain separate from host mock-MMIO evidence.

## Pure-Simple evidence and efficiency

The parity scenario in
`test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl` uses all
seven vectors. An equivalent isolated probe passed in interpreter mode during
development. `SIMPLE_COVERAGE=1` emitted an SDN artifact, but
the available binary identifies itself as the Rust bootstrap seed and its
aggregate artifact did not attribute decision records to the imported
platform module. Therefore this report claims 100% vector/MC/DC
condition evidence, not fabricated per-file runtime-probe percentages.  A
Pure-Simple Stage-4 coverage rerun remains required after bootstrap deployment.

The canonical decision core is O(1), performs six scalar mask comparisons,
allocates no memory, copies no aggregate data, and uses only direct dispatch.
The production C path was not changed.  The optimizer reported only normal MIR
dead-code-elimination opportunities for the core; no algorithm, allocation,
layout, loop-hoisting, or dispatch regression was introduced.  Timing/RSS
comparison is not meaningful for this test-only vector expansion and pure
scalar function addition, so no performance claim is made.
