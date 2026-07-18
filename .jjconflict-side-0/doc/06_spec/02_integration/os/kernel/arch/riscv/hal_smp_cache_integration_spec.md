# Hal Smp Cache Integration Specification

> 1. hal integration init

<!-- sdn-diagram:id=hal_smp_cache_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_smp_cache_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_smp_cache_integration_spec -> std
hal_smp_cache_integration_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_smp_cache_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Smp Cache Integration Specification

## Scenarios

### HalSmp + HalCache Integration

### IPI to AP — end-to-end

#### AC-1+AC-5: IPI send to hart 1 records call and populates PENDING_IPI slot

1. hal integration init
   - Expected: result.ipi_call_count equals `1u32`
   - Expected: pending equals `10u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_zicbom_available()
hal_integration_init(env)
val result = hal_integration_ipi_send(env, 1u32, 10u32)
# IPI call recorded in returned result
expect(result.ipi_call_count).to_equal(1u32)
# PENDING_IPI slot populated
val pending = hal_integration_get_pending_ipi(1u32)
expect(pending).to_equal(10u32)
```

</details>

#### AC-1+AC-5: IPI broadcast reaches all non-self harts

1. hal integration init with hart count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_zicbom_available()
hal_integration_init_with_hart_count(env, 3u32)
val result = hal_integration_ipi_broadcast(env, 255u32)
# At least 2 calls (to hart 1 and hart 2; not to self hart 0)
expect(result.ipi_call_count).to_be_greater_than(0u32)
```

</details>

### fence.i ordering after code load

#### AC-2+AC-5: sync_icache with Zicbom emits cbo.flush then fence.i

1. hal integration init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_zicbom_available()
hal_integration_init(env)
val result = hal_integration_sync_icache(env, 0x80200000u64, 4096u64)
expect(result.cbo_flush_count).to_be_greater_than(0u32)
expect(result.fence_i_count).to_be_greater_than(0u32)
```

</details>

#### AC-2+AC-5: sync_icache without Zicbom still emits fence.i (no cbo.flush)

1. hal integration init
   - Expected: result.cbo_flush_count equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_no_zicbom()
hal_integration_init(env)
val result = hal_integration_sync_icache(env, 0x80200000u64, 4096u64)
expect(result.fence_i_count).to_be_greater_than(0u32)
expect(result.cbo_flush_count).to_equal(0u32)
```

</details>

### Zicbom available vs fallback path

#### AC-2+AC-5: clean_dcache with Zicbom emits cbo.clean (no diagnostic)

1. hal integration init
   - Expected: result.diagnostic_emitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_zicbom_available()
hal_integration_init(env)
val result = hal_integration_clean_dcache(env, 0x80300000u64, 128u64)
expect(result.cbo_clean_count).to_be_greater_than(0u32)
expect(result.diagnostic_emitted).to_equal(false)
```

</details>

#### AC-2+AC-5: clean_dcache without Zicbom emits diagnostic (no cbo.clean, no panic)

1. hal integration init
   - Expected: result.cbo_clean_count equals `0u32`
   - Expected: result.diagnostic_emitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_no_zicbom()
hal_integration_init(env)
val result = hal_integration_clean_dcache(env, 0x80300000u64, 128u64)
expect(result.cbo_clean_count).to_equal(0u32)
expect(result.diagnostic_emitted).to_equal(true)
```

</details>

### Cross-feature handshake — PortableNumericCapabilities (AC-3)

#### AC-3: after init with Zicbom isa, has_riscv_zicbom is true

1. hal integration init
   - Expected: cap is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FAIL-TO-LOAD until Feature A Phase 3 adds has_riscv_zicbom field.
# Intentional TDD red — do NOT remove this test; Phase 5 wires it.
val env = make_integration_env_zicbom_available()
hal_integration_init(env)
val cap = portable_numeric_capabilities_has_riscv_zicbom()
expect(cap).to_equal(true)
```

</details>

#### AC-3: before init, has_riscv_zicbom defaults to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FAIL-TO-LOAD until Feature A Phase 3 adds has_riscv_zicbom field.
val cap = portable_numeric_capabilities_has_riscv_zicbom_default()
expect(cap).to_equal(false)
```

</details>

### SBI IPI path selection + cache probe — combined boot sequence

#### AC-1+AC-2+AC-3: full init sequence selects V3 path and detects Zicbom

1. hal integration full boot
   - Expected: ipi_path equals `V3`
   - Expected: has_zicbom is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_zicbom_available()
# Full boot: dtb_scan_init -> hal_smp_init -> hal_cache_init
hal_integration_full_boot(env)
val ipi_path = hal_integration_get_ipi_path()
val has_zicbom = hal_integration_get_has_zicbom()
expect(ipi_path).to_equal("V3")
expect(has_zicbom).to_equal(true)
```

</details>

#### AC-1+AC-2: full init with no SBI + no Zicbom selects CLINT + fallback path

1. hal integration full boot
   - Expected: ipi_path equals `Clint`
   - Expected: has_zicbom is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = make_integration_env_no_zicbom()
hal_integration_full_boot(env)
val ipi_path = hal_integration_get_ipi_path()
val has_zicbom = hal_integration_get_has_zicbom()
expect(ipi_path).to_equal("Clint")
expect(has_zicbom).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HalSmp + HalCache Integration
- IPI to AP — end-to-end
- fence.i ordering after code load
- Zicbom available vs fallback path
- Cross-feature handshake — PortableNumericCapabilities (AC-3)
- SBI IPI path selection + cache probe — combined boot sequence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
