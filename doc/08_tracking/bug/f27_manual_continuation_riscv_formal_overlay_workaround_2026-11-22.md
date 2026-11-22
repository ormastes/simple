# Workaround: f27 manual continuation of 10 modules via riscv_formal overlay

- **Date:** 2026-11-22
- **Status:** workaround
- **Severity:** P2

## Symptom

In Phase 3 build f27, 10 modules had to be compiled manually. `src/os/_QemuRunner/os_build_run.spl` failed HIR because its source base lacked fix a679b749ff6, which changes `src/lib/hardware/riscv_common/core/riscv_formal.spl`. 8 dependents cascaded, including `main_and_help`.

## Workaround

The manual continuation uses an overlay with release's fixed `riscv_formal.spl`.

## Removal condition

Remove the overlay when the Phase 3 to Phase 3 self-build runs from a base containing a679b749ff6.

## Related

f28's failure (`runtime_c_compile_pool_v1.spl` importing `cpu_count_checked` from `std.io_runtime`, introduced by e0aea49c8e9) is already fixed by #10777 (5d5c17bf4e0); no new row.
