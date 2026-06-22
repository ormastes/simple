# Hal Cache Specification

> <details>

<!-- sdn-diagram:id=hal_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_cache_spec -> std
hal_cache_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Cache Specification

## Scenarios

### HalCache

### hal_cache_sync_icache — fence.i always emitted

#### AC-2: emits fence.i when Zicbom not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: false, has_zicboz: false, has_zicbop: false)
val log = hal_cache_sync_icache_with_log(caps, 0x80200000u64, 4096u64)
expect(log.fence_i_count).to_be_greater_than(0u32)
```

</details>

#### AC-2: emits fence.i when Zicbom IS available (fence.i always runs)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_sync_icache_with_log(caps, 0x80200000u64, 4096u64)
expect(log.fence_i_count).to_be_greater_than(0u32)
```

</details>

#### AC-5: fence.i ordering — emitted after cbo.flush when Zicbom available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_sync_icache_with_log(caps, 0x80200000u64, 128u64)
expect(log.cbo_flush_count).to_be_greater_than(0u32)
expect(log.fence_i_count).to_be_greater_than(0u32)
```

</details>

### hal_cache_clean_dcache — cbo.clean per-line when Zicbom available

#### AC-2: emits cbo.clean for each cacheline in range when Zicbom=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80300000u64, 128u64, 64u32)
expect(log.cbo_clean_count).to_equal(2u32)
```

</details>

#### AC-2: cacheline count scales with range/stride

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80300000u64, 256u64, 64u32)
expect(log.cbo_clean_count).to_equal(4u32)
```

</details>

#### AC-2: emits diagnostic (no panic) when Zicbom=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: false, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80300000u64, 64u64, 64u32)
expect(log.cbo_clean_count).to_equal(0u32)
expect(log.diagnostic_emitted).to_equal(true)
```

</details>

#### AC-2: cacheline size from DTB cbom-block-size (not hardcoded 64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80400000u64, 256u64, 128u32)
expect(log.cbo_clean_count).to_equal(2u32)
```

</details>

### hal_cache_invalidate_dcache — cbo.inval per-line when Zicbom available

#### AC-2: emits cbo.inval for each cacheline when Zicbom=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_invalidate_dcache_with_log(caps, 0x80500000u64, 64u64, 64u32)
expect(log.cbo_inval_count).to_equal(1u32)
```

</details>

#### AC-2: emits diagnostic (no panic) when Zicbom=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = CmoCapSnapshot(has_zicbom: false, has_zicboz: false, has_zicbop: false)
val log = hal_cache_invalidate_dcache_with_log(caps, 0x80500000u64, 64u64, 64u32)
expect(log.cbo_inval_count).to_equal(0u32)
expect(log.diagnostic_emitted).to_equal(true)
```

</details>

### CMO probe ladder — 4 cases (AC-3, AC-5)

#### AC-3: DTB advertises Zicbom — probe returns true; cbo.clean emitted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = hal_cache_probe_with_isa("rv64gc_zicbom_zicboz")
expect(caps.has_zicbom).to_equal(true)
```

</details>

#### AC-3: DTB silent + illegal-instr probe fires — probe returns false; fallback no-op + diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = hal_cache_probe_with_trap_fires()
expect(caps.has_zicbom).to_equal(false)
```

</details>

#### AC-3: DTB silent + illegal-instr probe succeeds — probe returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = hal_cache_probe_with_trap_succeeds()
expect(caps.has_zicbom).to_equal(true)
```

</details>

#### AC-3: config flag disables CMO — probe returns false unconditionally

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = hal_cache_probe_with_cmo_disabled()
expect(caps.has_zicbom).to_equal(false)
```

</details>

### PortableNumericCapabilities handshake (AC-3, cross-feature)

#### AC-3: after hal_cache_init, has_riscv_zicbom is true on probe-positive path

1. hal cache init with isa
   - Expected: cap_value is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: PortableNumericCapabilities.has_riscv_zicbom does not exist yet.
# This test FAILS TO LOAD until Feature A Phase 3 adds the field.
# That is intentional TDD red. Phase 5 wires both together.
hal_cache_init_with_isa("rv64gc_zicbom")
val cap_value = portable_numeric_capabilities_has_riscv_zicbom()
expect(cap_value).to_equal(true)
```

</details>

#### AC-3: before any hal_cache_init, has_riscv_zicbom defaults to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap_value = portable_numeric_capabilities_has_riscv_zicbom_default()
expect(cap_value).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv/hal_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HalCache
- hal_cache_sync_icache — fence.i always emitted
- hal_cache_clean_dcache — cbo.clean per-line when Zicbom available
- hal_cache_invalidate_dcache — cbo.inval per-line when Zicbom available
- CMO probe ladder — 4 cases (AC-3, AC-5)
- PortableNumericCapabilities handshake (AC-3, cross-feature)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
