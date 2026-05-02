# FR-RISCV-HAL-PROD-WIRING-2026-05-02: Wire Real Production Bodies for HalSmp/HalCache

## Why

Phase 7 verify of `riscv_smp_cache_hal_phase1` found that AC-1 and AC-2 are
FAIL.  The commit `a2d0c3bcae` (Phase 5b lift-out) created the module files
and test-seam helpers but did NOT add the production-callable function bodies
that invoke real SBI / CMO instructions.

### AC-1 gap — HalSmp production bodies missing

In `src/os/kernel/arch/riscv64/hal_smp.spl` (147 lines), only `*_with_mock`
test-seam variants exist.  The following production functions are absent:

- `hal_smp_cpu_start(ap_id, entry, stack, arg) -> bool` — must store
  `HAL_SMP_BOOT_ARGS[ap_id]` then call `sbi_hart_start(ap_id, entry, ap_id)`
- `hal_smp_ipi_send(target, vector)` — must write `HAL_SMP_PENDING_IPI[target]`
  then call `sbi_probe_then_send_ipi(target)` from `sbi.spl`
- `hal_smp_ipi_broadcast(vector)` — must iterate all enabled harts (0..cpu_count)
  except self and call `sbi_probe_then_send_ipi` on each

Additionally `hal_smp_cpu_count()` (line 89-91) returns the cached
`HAL_SMP_CPU_COUNT_STATE` var; it does NOT call `dtb_scan.count_okay_cpus()`.
The init path `hal_smp_init_from_bytes` checks a magic sentinel (0xD00DFEED)
rather than actually parsing the DTB.

The rv32 mirror `src/os/kernel/arch/riscv32/hal_smp.spl` has the same gap.

### AC-2 gap — HalCache production bodies missing

In `src/os/kernel/arch/riscv64/hal_cache.spl` (137 lines), only `*_with_log`
test-seam variants exist.  The following production functions are absent:

- `hal_cache_sync_icache(addr, len)` — must call `cmo.fence_i()` always AND
  iterate `cbo_flush(addr)` per cacheline when `has_riscv_zicbom` is true
- `hal_cache_clean_dcache(addr, len)` — must call `cbo_clean` per cacheline
  if `has_riscv_zicbom`, else emit a runtime diagnostic and return
- `hal_cache_invalidate_dcache(addr, len)` — must call `cbo_inval` if available,
  fall back to `cbo_flush`, else emit diagnostic

The cacheline stride is hardcoded at 64 (line 107); it must instead read from
`dtb_scan.cbom_block_size(...)` (default 64 if the DTB property is absent).

The rv32 mirror `src/os/kernel/arch/riscv32/hal_cache.spl` has the same gap.

### AC-3 gap — PortableNumericCapabilities write-back

`hal_cache_init_with_isa` (line 96-99) writes into the module-local var
`ZICBOM_STATE`.  It does NOT write into a `PortableNumericCapabilities` struct
instance from `src/compiler/70.backend/portable_numeric_capabilities.spl`.
The compiler-level struct has `has_riscv_zicbom: bool` (line 43) but is
instantiated only in the compiler backend; there is no HAL-layer write path
into it.  AC-3 discriminator said "probe RESULT is assigned into a
PortableNumericCapabilities instance's fields" — that path does not exist.

## What

For each missing production function, add a body that:
1. Calls the real SBI or CMO helper (already present in `sbi.spl` / `cmo.spl`)
2. Uses the same state arrays already defined (HAL_SMP_BOOT_ARGS, HAL_SMP_PENDING_IPI, ZICBOM_STATE)
3. Reads `dtb_scan.cbom_block_size(...)` for cacheline stride in hal_cache_*

For AC-3: decide whether the HAL should write a kernel-local copy of a
`PortableNumericCapabilities`-shaped struct (simplest: rename `ZICBOM_STATE`
to a full struct and expose a getter matching Feature A's API contract), or
whether the compiler backend should poll a HAL-provided function at codegen
time (requires cross-layer coupling that may not be desirable).

## Files to modify

- `src/os/kernel/arch/riscv64/hal_smp.spl` — add production bodies
- `src/os/kernel/arch/riscv64/hal_cache.spl` — add production bodies
- `src/os/kernel/arch/riscv32/hal_smp.spl` — rv32 mirror (u32 addresses)
- `src/os/kernel/arch/riscv32/hal_cache.spl` — rv32 mirror

Optionally fix `hal_smp_init_from_bytes` to call real `dtb_scan.count_okay_cpus`
instead of the sentinel-magic path (currently test-only design).

## When

Apply in the next implementation phase of `riscv_smp_cache_hal_phase1` (or a
new follow-up feature).  Integration spec
`test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl`
has 10 failures — all requiring `hal_integration_init` and
`hal_integration_full_boot` functions that do not exist yet (same gap).

## Acceptance

AC-1, AC-2, AC-3 in `.sstack/riscv_smp_cache_hal_phase1/state.md` flip from
FAIL to PASS, and the integration spec passes all 10 tests.

Cross-links:
- `src/os/kernel/arch/riscv64/hal_smp.spl`
- `src/os/kernel/arch/riscv64/hal_cache.spl`
- `src/os/kernel/arch/riscv32/hal_smp.spl`
- `src/os/kernel/arch/riscv32/hal_cache.spl`
- `test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/riscv/sbi.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl`
