# RV64GC CPU Emulation — Non-Functional Requirements

**Date:** 2026-04-07
**Feature:** [rv64gc_cpu](../feature/rv64gc_cpu.md)

## NFR-RV64GC-001: ISA Compliance

The emulation must produce bit-identical results to QEMU `qemu-system-riscv64 -machine virt` for all implemented instructions. Verified by running the same test programs on both and comparing register state.

## NFR-RV64GC-002: IEEE 754 Compliance

Floating-point operations must match IEEE 754-2008:
- All 5 rounding modes
- All 5 exception flags (NV, DZ, OF, UF, NX)
- Canonical NaN propagation
- NaN-boxing for single-precision in double registers

## NFR-RV64GC-003: Test Coverage

- Unit test coverage: ≥80% branch coverage on all `src/hardware/rv64gc/` modules
- ~618 unit tests across 26 files
- 5 integration test files
- 1 comprehensive system test

## NFR-RV64GC-004: Simulation Performance

- Functional simulation: ≥1M instructions/sec on host
- Memory usage: ≤256MB RSS for single-hart 128MB RAM emulation
- Boot time: <1s to reach first UART output in QEMU virt profile

## NFR-RV64GC-005: Code Quality

- No files >800 lines (split if exceeded)
- No duplicate code (verified by `bin/simple duplicate-check`)
- No stubs in production code (pass_todo = hard fail)
- All public functions have sdoctest
