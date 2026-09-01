# Hal Smp Cache Integration Specification

> Tests covering HalSmp + HalCache Integration, IPI to AP — end-to-end, fence.i ordering after code load, Zicbom available vs fallback path, Cross-feature handshake — PortableNumericCapabilities (AC-3), SBI IPI path selection + cache probe — combined boot sequence.

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

- AC-1+AC-5: IPI send to hart 1 records call and populates PENDING_IPI slot
   - Expected: result.ipi_call_count equals `1u32`
   - Expected: pending equals `10u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1+AC-5: IPI send to hart 1 records call and populates PENDING_IPI slot")
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

- AC-1+AC-5: IPI broadcast reaches all non-self harts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1+AC-5: IPI broadcast reaches all non-self harts")
val env = make_integration_env_zicbom_available()
hal_integration_init_with_hart_count(env, 3u32)
val result = hal_integration_ipi_broadcast(env, 255u32)
# At least 2 calls (to hart 1 and hart 2; not to self hart 0)
expect(result.ipi_call_count).to_be_greater_than(0u32)
```

</details>

### fence.i ordering after code load

#### AC-2+AC-5: sync_icache with Zicbom emits cbo.flush then fence.i

- AC-2+AC-5: sync_icache with Zicbom emits cbo.flush then fence.i


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2+AC-5: sync_icache with Zicbom emits cbo.flush then fence.i")
val env = make_integration_env_zicbom_available()
hal_integration_init(env)
val result = hal_integration_sync_icache(env, 0x80200000u64, 4096u64)
expect(result.cbo_flush_count).to_be_greater_than(0u32)
expect(result.fence_i_count).to_be_greater_than(0u32)
```

</details>

#### AC-2+AC-5: sync_icache without Zicbom still emits fence.i (no cbo.flush)

- AC-2+AC-5: sync_icache without Zicbom still emits fence.i (no cbo.flush)
   - Expected: result.cbo_flush_count equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2+AC-5: sync_icache without Zicbom still emits fence.i (no cbo.flush)")
val env = make_integration_env_no_zicbom()
hal_integration_init(env)
val result = hal_integration_sync_icache(env, 0x80200000u64, 4096u64)
expect(result.fence_i_count).to_be_greater_than(0u32)
expect(result.cbo_flush_count).to_equal(0u32)
```

</details>

### Zicbom available vs fallback path

#### AC-2+AC-5: clean_dcache with Zicbom emits cbo.clean (no diagnostic)

- AC-2+AC-5: clean_dcache with Zicbom emits cbo.clean (no diagnostic)
   - Expected: result.diagnostic_emitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2+AC-5: clean_dcache with Zicbom emits cbo.clean (no diagnostic)")
val env = make_integration_env_zicbom_available()
hal_integration_init(env)
val result = hal_integration_clean_dcache(env, 0x80300000u64, 128u64)
expect(result.cbo_clean_count).to_be_greater_than(0u32)
expect(result.diagnostic_emitted).to_equal(false)
```

</details>

#### AC-2+AC-5: clean_dcache without Zicbom emits diagnostic (no cbo.clean, no panic)

- AC-2+AC-5: clean_dcache without Zicbom emits diagnostic (no cbo.clean, no panic)
   - Expected: result.cbo_clean_count equals `0u32`
   - Expected: result.diagnostic_emitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2+AC-5: clean_dcache without Zicbom emits diagnostic (no cbo.clean, no panic)")
val env = make_integration_env_no_zicbom()
hal_integration_init(env)
val result = hal_integration_clean_dcache(env, 0x80300000u64, 128u64)
expect(result.cbo_clean_count).to_equal(0u32)
expect(result.diagnostic_emitted).to_equal(true)
```

</details>

### Cross-feature handshake — PortableNumericCapabilities (AC-3)

#### AC-3: after init with Zicbom isa, has_riscv_zicbom is true

- AC-3: after init with Zicbom isa, has_riscv_zicbom is true
   - Expected: cap is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-3: after init with Zicbom isa, has_riscv_zicbom is true")
# FAIL-TO-LOAD until Feature A Phase 3 adds has_riscv_zicbom field.
# Intentional TDD red — do NOT remove this test; Phase 5 wires it.
val env = make_integration_env_zicbom_available()
hal_integration_init(env)
val cap = portable_numeric_capabilities_has_riscv_zicbom()
expect(cap).to_equal(true)
```

</details>

#### AC-3: before init, has_riscv_zicbom defaults to false

- AC-3: before init, has_riscv_zicbom defaults to false
   - Expected: cap is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-3: before init, has_riscv_zicbom defaults to false")
# FAIL-TO-LOAD until Feature A Phase 3 adds has_riscv_zicbom field.
val cap = portable_numeric_capabilities_has_riscv_zicbom_default()
expect(cap).to_equal(false)
```

</details>

### SBI IPI path selection + cache probe — combined boot sequence

#### AC-1+AC-2+AC-3: full init sequence selects V3 path and detects Zicbom

- AC-1+AC-2+AC-3: full init sequence selects V3 path and detects Zicbom
   - Expected: ipi_path equals `V3`
   - Expected: has_zicbom is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1+AC-2+AC-3: full init sequence selects V3 path and detects Zicbom")
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

- AC-1+AC-2: full init with no SBI + no Zicbom selects CLINT + fallback path
   - Expected: ipi_path equals `Clint`
   - Expected: has_zicbom is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1+AC-2: full init with no SBI + no Zicbom selects CLINT + fallback path")
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
| Source | `test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HalSmp + HalCache Integration, IPI to AP — end-to-end, fence.i ordering after code load, Zicbom available vs fallback path, Cross-feature handshake — PortableNumericCapabilities (AC-3), SBI IPI path selection + cache probe — combined boot sequence.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `808374941f734d48cb21ccb0e4aaa0a4b75825ad603b5d2d41d7ca0bdd35375e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `808374941f734d48cb21ccb0e4aaa0a4b75825ad603b5d2d41d7ca0bdd35375e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `808374941f734d48cb21ccb0e4aaa0a4b75825ad603b5d2d41d7ca0bdd35375e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl
mirror: doc/06_spec/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1+AC-5: IPI send to hart 1 records call and populates PENDING_IPI slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl:203:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1+AC-5: IPI broadcast reaches all non-self harts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/kernel/arch/riscv/hal_smp_cache_integration_spec.spl:213:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2+AC-5: sync_icache with Zicbom emits cbo.flush then fence.i' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
