# Simple RISC-V Hardening AC-5 — Dead Scratch Elimination

**Status:** TEST_BLOCKED

**Requirement:** `REQ-RISCV-HARDEN-005`

**Executable source:** `test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl`

**Evidence class:** source/product contract; not FPGA, QEMU, or Stage-4 qualification

## Purpose and audience

This manual tells RISC-V RTL maintainers how the executable system scenario
proves that the production RV32 VHDL generator and its checked-in golden no
longer contain the unreachable scratch array or payload-specific
return-address overrides.

## Preconditions

1. Run from the repository root.
2. Use an admitted pure-Simple full CLI; never substitute the Rust seed.
3. Keep the pinned RV32 golden at
   `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd`.
4. Treat any missing artifact, runtime error, nonzero exit, stale marker, or
   generator/golden byte mismatch as failure.

## Operator workflow

```sh
SIMPLE_BINARY="$STAGE4" "$STAGE4" test \
  test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl \
  --mode=interpreter

SIMPLE_BINARY="$STAGE4" "$STAGE4" spipe-docgen \
  test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl \
  --output doc/06_spec --no-index

SIMPLE_BINARY="$STAGE4" "$STAGE4" sspec-maintain scan \
  test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl
```

## Visible scenario flow

### 1. Production RV32 generation

1. Generate the production RV32 base core with debug taps enabled.
2. Confirm the artifact is the real `rv32_exec_core` and retains `rom_a` and
   `data_rom` ownership.
3. Apply the fail-closed dead-scratch contract and require no error.

### 2. Golden equivalence

1. Generate the RV32 base core and load the pinned golden.
2. Reject an empty, wrong-core, or stale golden.
3. Compare the complete artifacts byte-for-byte.

### 3. Debug-aspect edge

1. Generate the core with debug taps disabled and enabled.
2. Require the debug surface to differ as configured.
3. Require both products to remain scratch-free.

### 4. Deliberate stale-artifact rejection

1. Submit an empty artifact and require `RSH-AC5-E-NOT-RV32-CORE`.
2. Submit historical scratch geometry, storage, payload-register, and
   payload-address fragments independently.
3. Require the stable corresponding error for every stale class.

## Pass/fail contract

PASS requires four executed scenarios, all assertions green, a nonempty golden,
complete generated/golden equality, and no forbidden marker. `TEST_BLOCKED`, a
signal exit, a missing admitted CLI, or any error code is not PASS.

## Current evidence and blocker

On 2026-08-16 the admitted Stage-2 compiler (SHA-256
`2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`)
strictly built the generator with zero failed modules and no stub fallback, but
the resulting native artifact exited with signal 132 and
`runtime error: invalid field receiver`. Stage 2 cannot provide general
SSpec/docgen evidence, and no admitted full CLI was available. Therefore the
spec, docgen, and `sspec-maintain` runs remain honestly `TEST_BLOCKED`.

## Compatibility and limitations

The scenario covers only the structured RV32 base generator and pinned golden.
It does not prove FPGA timing, silicon boot, QEMU behavior, trap completeness,
or Stage-4 qualification. The flat-core comment-only update is protected by the
golden manifest and static guards, not promoted to a separate runtime claim.
