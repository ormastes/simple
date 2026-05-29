# RISC-V SMP + Cache HAL Spec

**Feature:** `riscv_smp_cache_hal_phase1`
**Phase:** 4-spec
**Date:** 2026-05-02

---

## Test Summary

| Spec File | Suite | Tests | AC Coverage |
|-----------|-------|-------|-------------|
| `test/unit/lib/baremetal/riscv/sbi_ipi_spec.spl` | SBI IPI Extension | 9 | AC-1 |
| `test/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl` | DTB CPU Walker | 12 | AC-1, AC-3, AC-5 |
| `test/unit/os/kernel/arch/riscv/hal_smp_spec.spl` | HalSmp | 10 | AC-1, AC-5 |
| `test/unit/os/kernel/arch/riscv/hal_cache_spec.spl` | HalCache | 13 | AC-2, AC-3, AC-5 |
| `test/unit/os/kernel/arch/riscv/per_cpu_tp_spec.spl` | Per-CPU tp Register | 7 | AC-4 |
| `test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl` | Integration | 10 | AC-1..AC-5 |

All tests are currently **TDD red** — no implementation exists. Phase 5 makes them green.

---

## Covered Scenarios

### SBI IPI probe ladder (sbi_ipi_spec.spl)
- IPI_PATH_V3: `sbi_probe_extension(0x735049)` returns available → V3 selected
- IPI_PATH_LEGACY: V3 absent, EID 0x04 available → Legacy selected
- IPI_PATH_CLINT: both absent → CLINT MMIO fallback at `0x02000000 + 4*hartid`
- Probe runs once; second probe does not re-query (memoised)
- Direct v3 and legacy send signatures accepted by shim

### DTB CPU walker (dtb_cpu_walker_spec.spl)
- 1, 2, 4-hart FDTs counted correctly
- `status="disabled"` hart excluded; no-status hart included
- All-disabled → fallback count = 1
- Null FDT pointer and bad magic → fallback count = 1
- `riscv,cbom-block-size` property read; default 64 when absent
- `riscv,isa` string containing `_zicbom` returned verbatim
- `dtb_scan_init` is idempotent

### HalSmp (hal_smp_spec.spl)
- `cpu_count` from DTB; fallback = 1 on null DTB
- `cpu_start` true on SBI_SUCCESS, false on SBI error
- `AP_BOOT_ARGS[ap_id]` populated with stack before SBI call
- `ipi_send` writes `vector` to `PENDING_IPI[target]` (global array, NOT tp+offset)
- `ipi_send` CLINT path records target hartid
- `ipi_broadcast` skips self; all non-self PENDING_IPI slots populated

### HalCache (hal_cache_spec.spl)
- `hal_cache_sync_icache`: fence.i always emitted; cbo.flush added if Zicbom
- `hal_cache_clean_dcache`: cbo.clean per-line when Zicbom; diagnostic (no panic) when absent
- `hal_cache_invalidate_dcache`: cbo.inval per-line when Zicbom; diagnostic when absent
- Cacheline stride from DTB; non-hardcoded-64 path verified
- CMO probe Case 1: DTB isa `_zicbom` → `has_zicbom = true`
- CMO probe Case 2: DTB silent + trap fires → `has_zicbom = false` + diagnostic
- CMO probe Case 3: DTB silent + trap succeeds → `has_zicbom = true`
- CMO probe Case 4: config-disabled → `has_zicbom = false` unconditionally
- `PortableNumericCapabilities.has_riscv_zicbom` written true after probe-positive init

### tp register (per_cpu_tp_spec.spl)
- tp = `per_cpu_base + hartid << shift` for BSP hart 0 and AP hart 1
- Different hartids produce different tp values (no aliasing)
- Hosted (non-baremetal) build: `simulate_tp_write_hosted` is a no-op
- Trap frame: x4 (tp) saved and restored correctly across entry/exit
- x4 slot not aliased with x3 (gp) or x5 (t0) in TrapFrame
- rv32: tp write uses 32-bit base

### Integration (hal_smp_cache_integration_spec.spl)
- IPI send to hart 1 records call and populates PENDING_IPI
- IPI broadcast reaches all non-self harts
- sync_icache: cbo.flush then fence.i (Zicbom); fence.i only (no Zicbom)
- clean_dcache: cbo.clean (Zicbom); diagnostic (no Zicbom)
- Cross-feature: `has_riscv_zicbom` true after Zicbom-positive init
- Cross-feature: `has_riscv_zicbom` defaults false before init
- Full boot sequence: V3 + Zicbom path; CLINT + no-Zicbom path

---

## Negative Markers

- Null FDT / bad magic → no crash; fallback values used
- `status="disabled"` hart → excluded from cpu_count
- `hal_smp_cpu_start` SBI failure → returns false (no panic)
- `hal_cache_clean_dcache` without Zicbom → diagnostic emitted; no panic; no cbo.clean
- `hal_cache_invalidate_dcache` without Zicbom → diagnostic; no cbo.inval; no panic
- CMO probe trap fires (Case 2) → `has_zicbom = false`; no illegal-instruction propagation
- Config-disabled CMO (Case 4) → `has_zicbom = false`; no CMO probe executed

No `to_raise` matchers used anywhere. All negative paths return observable sentinel values
(`bool`, `text`, `u32`) asserted via `to_equal` or `to_equal(false)`.

---

## Acceptance Markers

| AC | Spec File(s) | Status |
|----|-------------|--------|
| AC-1 | `sbi_ipi_spec.spl`, `hal_smp_spec.spl`, `hal_smp_cache_integration_spec.spl` | TDD red |
| AC-2 | `hal_cache_spec.spl`, `hal_smp_cache_integration_spec.spl` | TDD red |
| AC-3 | `hal_cache_spec.spl` (CMO probe + PortableNumericCapabilities), `hal_smp_cache_integration_spec.spl` | TDD red; FAIL-TO-LOAD until Feature A Phase 3 adds `has_riscv_zicbom` field |
| AC-4 | `per_cpu_tp_spec.spl` | TDD red |
| AC-5 | `dtb_cpu_walker_spec.spl`, `hal_smp_spec.spl`, `hal_cache_spec.spl`, `hal_smp_cache_integration_spec.spl` | TDD red |
| AC-6 | Not covered by spec tests (GHDL gate scripts — verified in Phase 7) | n/a |
| AC-7 | Not covered by spec tests (doc update — verified in Phase 7) | n/a |
