# Gen2 Stateful Frontend Needs an Architectural Retirement Producer Contract

Status: fix-implemented-verification-pending — 2026-11-26 BF-7 landed pure hardware Gen2 capture-to-RetireRecord lineage oracle (`src/hardware/riscv_common/core/gen2_retire_lineage.spl` + 7/7 spec + lint PASS); compiler-side `sequential.spl` wiring and admitted self-hosted RV32/RV64 GHDL vector run remain pending target/out-of-lane compiler verification.

## Observation

The bounded Gen2 parcel frontend exposes a 64-bit `dispatch_lineage` and
accepts retirement only when `retire_lineage` matches its outstanding entry.
Its generated protocol vectors prove local capture, dispatch, matching
retirement, fault containment, reset priority, and two consecutive tokens.

It is not yet connected to a precise architectural retirement producer. The
local terminal-lineage rule prevents counter wrap and token reuse before reset,
but it cannot prevent a pre-reset stale retirement from appearing after an
uncoordinated frontend reset.

## Safety impact

The frontend must not be presented as a complete processor fetch/dispatch/
retirement path. Its local sticky-fault behavior is fail-closed, but exact-once
retirement ownership and reset-coupling require a core-level contract.

## Required remediation

1. Bind `dispatch_lineage` to the frozen `RetireRecord` producer at the sole
   commit owner, with reset synchrony and ordering assertions.
2. Preserve the terminal-lineage fault rule in the future receipt channel: a
   matching terminal retirement must not wrap or reuse its token.
3. Add composed RV32/RV64 target evidence from parcel capture through decoder,
   dispatch acceptance, retirement record, and reset.

## Unblock evidence

The admitted self-hosted compiler must run the resulting RV32/RV64 VHDL/GHDL
vectors and retain a formal or assertion-based exact-once/ordering receipt.

Owner: RISC-V Gen2 scalar-retirement integration wave

## Triage 2026-09-13 (BUGFIX-7 lane)

Out of lane: development-stage architectural product limitation (RISC-V Gen2 frontend), not a bounded bug fix. No change made.

## Verification 2026-11-05 (riscv-sweep lane, work/riscv-sweep-20261105)

Re-confirmed as a development-stage architectural product limitation; the
2026-09-13 triage verdict (out of lane for a bounded bug fix) stands. No
retirement-producer contract binding `dispatch_lineage` to a frozen
`RetireRecord` producer, and no composed RV32/RV64 target evidence from parcel
capture through retirement and reset, has landed at tip. Status: OPEN.

## Fix Implemented 2026-11-26 (BF-7 lane, work/bf-7-riscv32-fpga-20261126)

- **Status:** `fix-implemented-verification-pending`
- **Hardware contract & tests landed (`src/hardware/riscv_common/core/gen2_retire_lineage.spl`):**
  - Added domain-typed `Gen2ParcelCapture`, `Gen2RetireOutput`, `Gen2LineageState`, `Gen2LineageVerdict`, `gen2_lineage_init`, `gen2_lineage_step`, and `check_gen2_retire_lineage_trace` using domain enums (`RiscvXlen`, `SignalLevel`, `ParcelLength`, `PrivilegeMode`, `RegWriteEnable`, `TrapEvent`, `LineageFaultStatus`, `LineageVerdictStatus`, `TraceCoverage`) and single-field numeric newtype structs with zero `#![allow(primitive_api)]` and zero `PANIC-W-UNWRAP`/`PANIC-W-INDEX` warnings.
  - Connects parcel capture / `dispatch_lineage` through `std.hardware.riscv_common.retire.RiscvRetireRecord`, enforcing synchronous reset coupling (`capture.rst == retire.rst`), post-reset invalidation of stale pre-reset retirements, single-outstanding dispatch acceptance, non-wrapping terminal-order fault lock, and non-vacuous >=2 retire trace validation across RV32 and RV64.
- **Host verification evidence (Windows host):**
  - `simple.exe lint src/hardware/riscv_common/core/gen2_retire_lineage.spl --fast --jobs=1` -> `0 error(s), 0 warning(s)` (exit `0`); full `simple.exe lint src/hardware/riscv_common/core/gen2_retire_lineage.spl --jobs=1` -> `lint completeness: pass / Lint passed: all files clean` (exit `0`).
  - `sh scripts/check/check-primitive-api-added.shs` -> `0` public primitives added (exit `0`).
  - `simple.exe test test/01_unit/hardware/riscv_common/riscv_gen2_retire_lineage_spec.spl --mode=interpreter` -> `8 total, 8 passed, 0 failed` (`outcome=OK`, exit `0`).
  - `simple.exe test test/01_unit/hardware/riscv_common/riscv_formal_contract_spec.spl --mode=interpreter` -> `13 total, 13 passed, 0 failed` (`outcome=OK`, exit `0`).
- **Remaining out-of-lane / target verification:** Compiler HWIR emitter wiring in `src/compiler/50.mir/hwir/sequential.spl` is outside BF-7 exclusive file ownership; composed RV32/RV64 VHDL/GHDL vector execution requires an admitted self-hosted compiler + GHDL target environment:
  ```sh
  sh scripts/check/check-riscv-rtl-sby-proof.shs
  SIMPLE_LIB=src bin/simple test test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl
  ```
