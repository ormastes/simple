# Hal Cache Specification

> Tests covering HalCache, hal_cache_sync_icache — fence.i always emitted, hal_cache_clean_dcache — cbo.clean per-line when Zicbom available, hal_cache_invalidate_dcache — cbo.inval per-line when Zicbom available, CMO probe ladder — 4 cases (AC-3, AC-5), PortableNumericCapabilities handshake (AC-3, cross-feature).

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

- AC-2: emits fence.i when Zicbom not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: emits fence.i when Zicbom not available")
val caps = CmoCapSnapshot(has_zicbom: false, has_zicboz: false, has_zicbop: false)
val log = hal_cache_sync_icache_with_log(caps, 0x80200000u64, 4096u64)
expect(log.fence_i_count).to_be_greater_than(0u32)
```

</details>

#### AC-2: emits fence.i when Zicbom IS available (fence.i always runs)

- AC-2: emits fence.i when Zicbom IS available (fence.i always runs)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: emits fence.i when Zicbom IS available (fence.i always runs)")
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_sync_icache_with_log(caps, 0x80200000u64, 4096u64)
expect(log.fence_i_count).to_be_greater_than(0u32)
```

</details>

#### AC-5: fence.i ordering — emitted after cbo.flush when Zicbom available

- AC-5: fence.i ordering — emitted after cbo.flush when Zicbom available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: fence.i ordering — emitted after cbo.flush when Zicbom available")
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_sync_icache_with_log(caps, 0x80200000u64, 128u64)
expect(log.cbo_flush_count).to_be_greater_than(0u32)
expect(log.fence_i_count).to_be_greater_than(0u32)
```

</details>

### hal_cache_clean_dcache — cbo.clean per-line when Zicbom available

#### AC-2: emits cbo.clean for each cacheline in range when Zicbom=true

- AC-2: emits cbo.clean for each cacheline in range when Zicbom=true
   - Expected: log.cbo_clean_count equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: emits cbo.clean for each cacheline in range when Zicbom=true")
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80300000u64, 128u64, 64u32)
expect(log.cbo_clean_count).to_equal(2u32)
```

</details>

#### AC-2: cacheline count scales with range/stride

- AC-2: cacheline count scales with range/stride
   - Expected: log.cbo_clean_count equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: cacheline count scales with range/stride")
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80300000u64, 256u64, 64u32)
expect(log.cbo_clean_count).to_equal(4u32)
```

</details>

#### AC-2: emits diagnostic (no panic) when Zicbom=false

- AC-2: emits diagnostic (no panic) when Zicbom=false
   - Expected: log.cbo_clean_count equals `0u32`
   - Expected: log.diagnostic_emitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: emits diagnostic (no panic) when Zicbom=false")
val caps = CmoCapSnapshot(has_zicbom: false, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80300000u64, 64u64, 64u32)
expect(log.cbo_clean_count).to_equal(0u32)
expect(log.diagnostic_emitted).to_equal(true)
```

</details>

#### AC-2: cacheline size from DTB cbom-block-size (not hardcoded 64)

- AC-2: cacheline size from DTB cbom-block-size (not hardcoded 64)
   - Expected: log.cbo_clean_count equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: cacheline size from DTB cbom-block-size (not hardcoded 64)")
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_clean_dcache_with_log(caps, 0x80400000u64, 256u64, 128u32)
expect(log.cbo_clean_count).to_equal(2u32)
```

</details>

### hal_cache_invalidate_dcache — cbo.inval per-line when Zicbom available

#### AC-2: emits cbo.inval for each cacheline when Zicbom=true

- AC-2: emits cbo.inval for each cacheline when Zicbom=true
   - Expected: log.cbo_inval_count equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: emits cbo.inval for each cacheline when Zicbom=true")
val caps = CmoCapSnapshot(has_zicbom: true, has_zicboz: false, has_zicbop: false)
val log = hal_cache_invalidate_dcache_with_log(caps, 0x80500000u64, 64u64, 64u32)
expect(log.cbo_inval_count).to_equal(1u32)
```

</details>

#### AC-2: emits diagnostic (no panic) when Zicbom=false

- AC-2: emits diagnostic (no panic) when Zicbom=false
   - Expected: log.cbo_inval_count equals `0u32`
   - Expected: log.diagnostic_emitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: emits diagnostic (no panic) when Zicbom=false")
val caps = CmoCapSnapshot(has_zicbom: false, has_zicboz: false, has_zicbop: false)
val log = hal_cache_invalidate_dcache_with_log(caps, 0x80500000u64, 64u64, 64u32)
expect(log.cbo_inval_count).to_equal(0u32)
expect(log.diagnostic_emitted).to_equal(true)
```

</details>

### CMO probe ladder — 4 cases (AC-3, AC-5)

#### AC-3: DTB advertises Zicbom — probe returns true; cbo.clean emitted

- AC-3: DTB advertises Zicbom — probe returns true; cbo.clean emitted
   - Expected: caps.has_zicbom is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: DTB advertises Zicbom — probe returns true; cbo.clean emitted")
val caps = hal_cache_probe_with_isa("rv64gc_zicbom_zicboz")
expect(caps.has_zicbom).to_equal(true)
```

</details>

#### AC-3: DTB silent + illegal-instr probe fires — probe returns false; fallback no-op + diagnostic

- AC-3: DTB silent + illegal-instr probe fires — probe returns false; fallback no-op + diagnostic
   - Expected: caps.has_zicbom is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: DTB silent + illegal-instr probe fires — probe returns false; fallback no-op + diagnostic")
val caps = hal_cache_probe_with_trap_fires()
expect(caps.has_zicbom).to_equal(false)
```

</details>

#### AC-3: DTB silent + illegal-instr probe succeeds — probe returns true

- AC-3: DTB silent + illegal-instr probe succeeds — probe returns true
   - Expected: caps.has_zicbom is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: DTB silent + illegal-instr probe succeeds — probe returns true")
val caps = hal_cache_probe_with_trap_succeeds()
expect(caps.has_zicbom).to_equal(true)
```

</details>

#### AC-3: config flag disables CMO — probe returns false unconditionally

- AC-3: config flag disables CMO — probe returns false unconditionally
   - Expected: caps.has_zicbom is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: config flag disables CMO — probe returns false unconditionally")
val caps = hal_cache_probe_with_cmo_disabled()
expect(caps.has_zicbom).to_equal(false)
```

</details>

### PortableNumericCapabilities handshake (AC-3, cross-feature)

#### AC-3: after hal_cache_init, has_riscv_zicbom is true on probe-positive path

- AC-3: after hal_cache_init, has_riscv_zicbom is true on probe-positive path
   - Expected: cap_value is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: after hal_cache_init, has_riscv_zicbom is true on probe-positive path")
# NOTE: PortableNumericCapabilities.has_riscv_zicbom does not exist yet.
# This test FAILS TO LOAD until Feature A Phase 3 adds the field.
# That is intentional TDD red. Phase 5 wires both together.
hal_cache_init_with_isa("rv64gc_zicbom")
val cap_value = portable_numeric_capabilities_has_riscv_zicbom()
expect(cap_value).to_equal(true)
```

</details>

#### AC-3: before any hal_cache_init, has_riscv_zicbom defaults to false

- AC-3: before any hal_cache_init, has_riscv_zicbom defaults to false
   - Expected: cap_value is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: before any hal_cache_init, has_riscv_zicbom defaults to false")
val cap_value = portable_numeric_capabilities_has_riscv_zicbom_default()
expect(cap_value).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/riscv/hal_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HalCache, hal_cache_sync_icache — fence.i always emitted, hal_cache_clean_dcache — cbo.clean per-line when Zicbom available, hal_cache_invalidate_dcache — cbo.inval per-line when Zicbom available, CMO probe ladder — 4 cases (AC-3, AC-5), PortableNumericCapabilities handshake (AC-3, cross-feature).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bf5cceab271bcb169fa299548a8a695a0db7df0d4b182ad7621f4d73db379546`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf5cceab271bcb169fa299548a8a695a0db7df0d4b182ad7621f4d73db379546`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf5cceab271bcb169fa299548a8a695a0db7df0d4b182ad7621f4d73db379546`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/riscv/hal_cache_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/riscv/hal_cache_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/riscv/hal_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/riscv/hal_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/riscv/hal_cache_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: emits fence.i when Zicbom not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv/hal_cache_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: emits fence.i when Zicbom IS available (fence.i always runs)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv/hal_cache_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: fence.i ordering — emitted after cbo.flush when Zicbom available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
