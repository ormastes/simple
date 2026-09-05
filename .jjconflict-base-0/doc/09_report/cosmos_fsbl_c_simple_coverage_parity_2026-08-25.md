# Cosmos FSBL C / Pure-Simple coverage parity — 2026-08-25

## Current status

**Evidence and production-cutover acceptance remain open.** The cutover work
selects `src/os/kernel/arch/arm32/cosmos/cosmos_fsbl.spl` for the production
source manifest and link, while retaining `cosmos_fsbl.c` only as an unbuilt C
provenance baseline. This update does not contain or imply a new PASS receipt.

The earlier development run reported 14/14 input-reachable C arcs and seven
passing semantic vectors, but retained neither its raw artifacts nor admissible
Pure-Simple provenance. Those observations remain historical diagnostics.

## Shared semantics and C-oracle provenance

`test/fixtures/os/cosmos/fsbl_handoff_vectors.tsv` is the single seven-row
decimal input table consumed by the C host harness and the Simple SSpec. It has
one all-good row and six rows that independently invalidate SLCR lock, ARM
clock, DDR clock, PS primary reset, A9 CPU0 reset, or DEVCFG PCFG_DONE.

The test-only `cosmos_fsbl_oracle.c` is an extraction of the retained C
baseline, not a second implementation. The direct host runner and coverage
producer hash its text from the exact first `#include "cosmos_hal.h"` line
through EOF and refuse to run unless that hash equals the same extraction from
`cosmos_fsbl.c`. The retained receipt binds the oracle file, baseline file, and
shared semantic hash; the independent checker recomputes all three.

The producer and checker also fail closed unless the candidate's ABI status
values, MMIO bases/offsets, and decision masks retain their exact C-header
contracts. The unit contract pins the same mappings independently.

The test-only C oracle and Pure-Simple decision core evaluate the same six
predicates as ordered scalar fail-closed guards. This retains the original
short-circuit order while making each condition outcome directly attributable.
Both hot paths remain O(1), use scalar register values, perform no allocation
or aggregate copy, and add no production instrumentation.

## Evidence commands

With a current provenance-admitted full Stage-4 Pure-Simple CLI:

```sh
SIMPLE_BINARY=/absolute/path/to/stage4/simple \
  sh scripts/check/produce-cosmos-fsbl-fail-closed-coverage.shs
sh scripts/check/check-cosmos-fsbl-fail-closed-coverage-receipt.shs
SIMPLE_BINARY=/absolute/path/to/stage4/simple \
  sh test/02_integration/os/cosmos/run_pure_simple_arm32_emit_object_test.shs
```

The coverage producer measures only the six FSBL fail-closed C guards with
GCC/gcov and the six Simple decision/condition rows. It requires 12/12 C
branch arcs and dual outcomes for exactly six Simple decisions and six
conditions. It adds no production instrumentation. The ARM32 runner separately
requires an ELF32 ARM hard-float ET_REL object for the cutover source, both
historical C exports, real consumer relocations, successful `ld.lld -r`
combination with the two ABI/runtime shims, and no remaining undefined symbols.

## Claim boundary

Only a newly produced and independently accepted receipt can prove host-level
decision parity for these six guards. A passing ARM32 runner would additionally
admit relocatable linkage of the cutover source. Neither proves BootROM
handoff, physical clocks/DDR/reset/PL behavior, full Cosmos HAL I/O parity,
whole-HAL branch/condition coverage, x86 bootstrap reproducibility, or the
production build/package cutover.

The C oracle lives at `test/fixtures/os/cosmos/cosmos_fsbl_oracle.c` and is
never included in the production source manifest or link. The cutover work is
intended to export the historical `cosmos_fsbl_validate_handoff` and
`cosmos_fsbl_selftest` ABI from
`src/os/kernel/arch/arm32/cosmos/cosmos_fsbl.spl`; no admission is claimed
until the ARM32 object and production link/package gates pass. Its six scalar
decisions live alone in
`src/os/kernel/arch/arm32/cosmos/cosmos_fsbl_decision.spl`, preventing the
firmware closure from retaining descriptor text, arrays, or printing code.

`doc/08_tracking/bug/pure_simple_arm32_emit_object_ignored_2026-08-24.md`
remains applicable until admitted ARM32 object and final-link evidence closes
that blocker. This source migration must not be reported as verified before
that evidence exists.
