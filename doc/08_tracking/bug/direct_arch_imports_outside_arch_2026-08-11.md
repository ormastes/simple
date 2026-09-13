# 7 direct arch imports outside `arch/` (AC-3 violation)

**Date:** 2026-08-11
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Severity:** Medium (portability contract)

## Summary

`src/os/port/multiarch_audit_report.spl` previously PRINTED
`"direct_arch_imports_outside_arch": 0` as a hardcoded string literal. It
measured nothing, and every spec asserting against that literal was green
unconditionally.

The generator now scans the real sources. The measured value is **7**, not 0.

## How it was fake

`src/os/port/multiarch_audit_report.spl:20` (pre-fix):

```
"  \"direct_arch_imports_outside_arch\": 0,\n" +
```

A string constant. No file was read, nothing was counted. Three specs asserted
`report.contains("\"direct_arch_imports_outside_arch\": 0")` against it.

## Measured violations (2026-08-11)

Modules outside `src/os/kernel/arch/` and `src/os/kernel/arch_adapt/` that
import an arch-family module directly:

| File | Line |
|------|------|
| `src/os/compositor/arm64_virtio_input_backend.spl` | 35 |
| `src/os/kernel/boot/riscv_services.spl` | 7 |
| `src/os/kernel/loader/x86_64_fs_exec_ring3.spl` | 41 |
| `src/os/kernel/memory/user_address_space.spl` | 93 |
| `src/os/kernel/memory/user_address_space.spl` | 103 |
| `src/os/services/audio/audio_service.spl` | 29 |
| `src/os/services/audio/audio_service.spl` | 30 |

Cross-checked with an independent shell scan: same count, same 7 file:line
pairs.

## Failing spec

`test/01_unit/os/multiarch/hal_trait_surface_spec.spl` — "report shows zero
arch-specific imports outside arch/". Mirrored at
`test/unit/os/multiarch/hal_trait_surface_spec.spl`.

The AC-3 assertion is deliberately left at `0`. It is a correct spec failing on
real drift. **Do not relax the number to obtain green** — remove the imports.

## Fail-closed proof

Injecting `src/os/_gate_probe_violation.spl` containing
`use os.kernel.arch.x86_64.boot.{probe}` moved the measured count 7 → 8 and
listed the probe file in `direct_arch_import_samples`. Removing it returned the
count to 7 with zero residue.

A positive control ("loc report is a real measurement, not a static literal")
asserts `arch_import_files_scanned` and `direct_arch_import_samples` are present
and non-trivial, so a regression back to a hardcoded literal — or a missing
report file — fails loudly instead of passing vacuously.

## Unblock condition

Route all 7 imports through `os.kernel.arch.hal` (or `arch_adapt/`), re-run
`bin/simple run src/os/port/multiarch_audit_report.spl`, and confirm the report
reads `"direct_arch_imports_outside_arch": 0`. The spec then goes green on its
own with no edit.

## Re-check 2026-09-13 (BUGFIX-7 lane)

`bin/simple run src/os/port/multiarch_audit_report.spl` -> `build/multiarch/arch_loc_report.json`:
`"direct_arch_imports_outside_arch": 8` (drifted from the original 7 — file
set changed: `virtio_rng_mmio.spl:4`, `riscv_services.spl:7`,
`tcp_baremetal_min.spl:7`, `riscv64_fs_exec_spawn.spl:16`,
`x86_64_server_first_dispatch.spl:9`, `user_address_space.spl:93,102`,
`vmm_core.spl:520`). Still reproduces, still real drift.

Checked feasibility of the "route through `os.kernel.arch.hal`" unblock
condition: `os.kernel.arch.hal` (`src/os/kernel/arch/hal.spl`) is a generic,
already-populated HAL surface (`hal_paging_map`, `hal_flush_tlb`,
`hal_context_save`, ...) with no equivalents for any of these 8 imports
(`rv32_admit_secure_entropy_candidate`, `riscv64_display_initialize`,
`rv64_boot_tcp_policy_link_anchor`, `Rv64ProcessStdoutResult`,
`validate_enter_user_blocking_handoff`, `riscv64_vmm_map_page_in`,
`hal_x86_64_read_cr3_raw`/`hal_x86_64_write_cr3_raw`). Adding portable
equivalents for 8 distinct, arch-specific one-off APIs (entropy source,
display init, TCP boot policy, process-stdout capture, user-entry
validation, page mapping, CR3 access) is a real HAL design task per symbol,
not a mechanical import rewrite — out of this lane's per-bug budget. Left
OPEN, no change made.
