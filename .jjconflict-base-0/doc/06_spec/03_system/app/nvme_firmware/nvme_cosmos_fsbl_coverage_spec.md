# Cosmos FSBL runtime branch evidence receipt

This host-only gate measures two bounded owners:

- `src/os/kernel/arch/arm32/cosmos/cosmos_fsbl.c`, as a separate 2/2 LLVM
  profile/coverage slice over the real acquisition bridge; and
- `src/os/kernel/arch/arm32/cosmos/cosmos_fsbl.spl`, compiled by an admitted
  Stage-4 self-host into a retained production policy object and linked into a
  mixed C/Simple harness. The 12 real policy decisions update a 24-outcome
  runtime mask at the point each condition is evaluated. The harness can reset
  and read the mask through the existing coverage-test bridge, but cannot
  declare a hit.

The receipt records source, emitted-object, compiler, provenance, and raw-output
SHA-256 values. It also pins every Simple decision ID to the exact source line
and column of both its production instrumentation call and following branch.
Validation
requires the C bridge to remain exactly 2/2 and the executed Simple object to
emit 24/24 outcomes. A sabotage check removes one outcome from otherwise
self-consistent raw evidence and proves the validator rejects it.

This is not physical-board evidence and is not a whole-HAL coverage claim.

## Operator command

```sh
sh scripts/check/check-cosmos-fsbl-coverage.shs
```

Success ends with:

```text
STATUS: PASS cosmos-fsbl scoped runtime branch evidence
```

A bootstrap seed is rejected and is never promoted into coverage authority.
Physical-board evidence remains separate; this is not a whole-HAL claim.
