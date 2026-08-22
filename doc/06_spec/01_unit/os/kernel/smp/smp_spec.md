# SMP kernel scaffolding

> The SMP scaffold owns logical CPU discovery, AP startup bookkeeping, online CPU state, pending IPI masks, and the preemption disable counter used by scheduler and green-carrier wakeup paths. These tests exercise the interpreter-safe public API rather than importing private constants or mutating per-CPU globals directly.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMP kernel scaffolding

The SMP scaffold owns logical CPU discovery, AP startup bookkeeping, online CPU state, pending IPI masks, and the preemption disable counter used by scheduler and green-carrier wakeup paths. These tests exercise the interpreter-safe public API rather than importing private constants or mutating per-CPU globals directly.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE4-G18 |
| Category | Kernel / SMP |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/01_unit/os/kernel/smp/smp_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# SMP kernel scaffolding
**Feature IDs:** #WAVE4-G18
**Category:** Kernel / SMP

## Overview

The SMP scaffold owns logical CPU discovery, AP startup bookkeeping, online CPU
state, pending IPI masks, and the preemption disable counter used by scheduler
and green-carrier wakeup paths. These tests exercise the interpreter-safe
public API rather than importing private constants or mutating per-CPU globals
directly.

## Examples

The spec initializes BSP state, brings an AP online, registers firmware APIC
ids, records AP startup progress, sends and drains IPI bitmasks, and verifies
the named IPI accessors used by scheduler-facing code.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### smp_init
_Verify that smp_init sets up the per-CPU table with BSP online and all APs offline._

#### BSP alone is online after init

- Verify: BSP alone is online after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: BSP alone is online after init")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
expect smp_online_count().to_equal(1u32)
expect percpu_is_online(0u32).to_equal(true)
expect percpu_is_online(1u32).to_equal(false)
```

</details>

### smp_bringup_ap

#### brings a second CPU online

- Verify: brings a second CPU online


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: brings a second CPU online")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
val ok = smp_bringup_ap(1u32)
expect ok.to_equal(true)
expect smp_online_count().to_equal(2u32)
```

</details>

#### refuses to bring up cpu 0 (BSP is already online)

- Verify: refuses to bring up cpu 0 (BSP is already online)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: refuses to bring up cpu 0 (BSP is already online)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
val ok = smp_bringup_ap(0u32)
expect ok.to_equal(false)
```

</details>

#### refuses cpu_id >= MAX_CPUS

- Verify: refuses cpu_id >= MAX_CPUS


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: refuses cpu_id >= MAX_CPUS")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
val ok = smp_bringup_ap(percpu_max_cpus())
expect ok.to_equal(false)
```

</details>

### firmware APIC registration

#### records firmware APIC ids without marking APs online

- Verify: records firmware APIC ids without marking APs online


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: records firmware APIC ids without marking APs online")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()

val count = smp_register_firmware_apic_ids([4u32, 9u32, 13u32])

expect count.to_equal(3u32)
expect smp_num_cpus().to_equal(3u32)
expect percpu_is_present(2u32).to_equal(true)
val cpu_apic_id = percpu_apic_id(1u32).unwrap()
expect cpu_apic_id.to_equal(9u32)
expect percpu_is_online(1u32).to_equal(false)
expect smp_online_count().to_equal(1u32)
```

</details>

#### tracks AP startup and marks online by APIC id

- Verify: tracks AP startup and marks online by APIC id


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: tracks AP startup and marks online by APIC id")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
smp_register_firmware_apic_ids([4u32, 9u32, 13u32])

expect smp_mark_ap_startup_sent(1u32).to_equal(true)
expect smp_ap_startup_sent(1u32).to_equal(true)
expect smp_mark_ap_started_by_apic_id(13u32).to_equal(true)

expect percpu_is_online(2u32).to_equal(true)
expect smp_online_count().to_equal(2u32)
```

</details>

#### rejects unknown APIC ids

- Verify: rejects unknown APIC ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: rejects unknown APIC ids")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
smp_register_firmware_apic_ids([4u32, 9u32])

expect smp_mark_ap_started_by_apic_id(99u32).to_equal(false)
```

</details>

#### reports when registered APs need automatic boot startup

- Verify: reports when registered APs need automatic boot startup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: reports when registered APs need automatic boot startup")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
expect x86_registered_ap_boot_startup_needed().to_equal(false)

smp_register_firmware_apic_ids([4u32, 9u32])

expect x86_registered_ap_boot_startup_needed().to_equal(true)
```

</details>

### smp IPIs
_IPI send/take and bitmask accumulation via g_percpu[].ipi_pending._

#### send/take round-trips the reason bitmask

- Verify: send/take round-trips the reason bitmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: send/take round-trips the reason bitmask")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
smp_bringup_ap(1u32)
val sent = smp_send_ipi(1u32, smp_ipi_resched())
expect sent.to_equal(true)
val got = smp_take_ipi(1u32)
expect got.to_equal(smp_ipi_resched())
```

</details>

#### multiple IPIs OR into the pending mask

- Verify: multiple IPIs OR into the pending mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: multiple IPIs OR into the pending mask")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
smp_bringup_ap(1u32)
smp_send_ipi(1u32, smp_ipi_resched())
smp_send_ipi(1u32, smp_ipi_tlb_flush())
val got = smp_take_ipi(1u32)
val combined: u32 = smp_ipi_resched() | smp_ipi_tlb_flush()
expect got.to_equal(combined)
```

</details>

#### take_ipi clears the pending mask

- Verify: take_ipi clears the pending mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: take_ipi clears the pending mask")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
smp_bringup_ap(1u32)
smp_send_ipi(1u32, smp_ipi_halt())
smp_take_ipi(1u32)
val got2 = smp_take_ipi(1u32)
expect got2.to_equal(0u32)
```

</details>

#### send_ipi to offline CPU returns false

- Verify: send_ipi to offline CPU returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: send_ipi to offline CPU returns false")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
val sent = smp_send_ipi(5u32, smp_ipi_resched())
expect sent.to_equal(false)
```

</details>

### preemption counter

#### disable nests and enable decrements

- Verify: disable nests and enable decrements


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: disable nests and enable decrements")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
smp_init()
expect percpu_preempt_enabled(0u32).to_equal(true)
percpu_preempt_disable(0u32)
expect percpu_preempt_enabled(0u32).to_equal(false)
percpu_preempt_disable(0u32)
percpu_preempt_enable(0u32)
expect percpu_preempt_enabled(0u32).to_equal(false)
percpu_preempt_enable(0u32)
expect percpu_preempt_enabled(0u32).to_equal(true)
```

</details>

### IPI reason constants

#### have stable bit assignments

- Verify: have stable bit assignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SMP_SMP-001
step("Verify: have stable bit assignments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect smp_ipi_resched().to_equal(0x1u32)
expect smp_ipi_tlb_flush().to_equal(0x2u32)
expect smp_ipi_halt().to_equal(0x4u32)
expect smp_ipi_call_func().to_equal(0x8u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Research:** `doc/01_research/local/multicore_green.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bdfeb2ba8454664250d361d4eca64c6daf30216979ba3cae64d789413f2b6794`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bdfeb2ba8454664250d361d4eca64c6daf30216979ba3cae64d789413f2b6794`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bdfeb2ba8454664250d361d4eca64c6daf30216979ba3cae64d789413f2b6794`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/smp/smp_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/smp/smp_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/smp/smp_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/smp/smp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/smp/smp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
