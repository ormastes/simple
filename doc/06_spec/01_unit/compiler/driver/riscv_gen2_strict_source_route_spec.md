# RISC-V Gen2 Strict Source VHDL Route

Executable companion: `test/01_unit/compiler/driver/riscv_gen2_strict_source_route_spec.spl`.

## Purpose

This focused unit specification exercises `CompilerDriver` directly for a
hardware-tagged source file in the critical Gen2 VHDL route. The public source
facade is intentionally not its oracle because that facade retains a legacy
subset fallback. The test observes only the direct compiler result and whether
the requested VHDL artifact bundle was created.

## Evidence steps

1. Compile valid frontend hardware source with critical policy but no concrete
   target; require `HWIR-E-CRITICAL-CONFIG` and no VHDL, map, or manifest.
2. Compile the same source with unsupported target `rv99`; require
   `HWIR-E-CORE-CONFIG` and no artifact bundle.
3. Compile the same source with target `rv32`. Its addition is outside the
   deliberately closed strict-HWIR instruction subset; require
   `HWIR-E-CRITICAL-LOWER` and `HWIR-E-MIR-INSTRUCTION`, with no legacy VHDL
   fallback or artifact bundle.

## Requirement traceability

- REQ-G2-002 — concrete target validation.
- REQ-G2-003 — strict lowering fails diagnostically without fallback.
- REQ-G2-005 — strict Gen2 requests never invoke the legacy V1 route.
- REQ-G2-006 — critical source requests require explicit RV32/RV64 target.
- NFR-G2-002 — invalid input fails closed with actionable diagnostics.
- NFR-G2-005 — legacy V1 generators remain isolated from strict requests.
- NFR-G2-006 — critical Gen2 source routing fails closed before legacy VHDL.

## Evidence status

This is a unit-level direct compiler oracle, not a generated-VHDL
qualification receipt. Bootstrap-seed execution is diagnostic only; release
qualification requires the admitted self-hosted critical-mode route and the
system-test evidence defined for the Gen2 HWIR foundation.
