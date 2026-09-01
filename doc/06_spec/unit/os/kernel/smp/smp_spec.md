# SMP kernel scaffolding

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMP kernel scaffolding

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE4-G18 |
| Category | Kernel / SMP |
| Status | Active |
| Source | `test/unit/os/kernel/smp/smp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### smp_init

#### BSP alone is online after init

- BSP alone is online after init
   - Expected: smp_online_count() equals `1u32`
   - Expected: percpu_is_online(0u32) is true
   - Expected: percpu_is_online(1u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BSP alone is online after init")
smp_init()
expect(smp_online_count()).to_equal(1u32)
expect(percpu_is_online(0u32)).to_equal(true)
expect(percpu_is_online(1u32)).to_equal(false)
```

</details>

### smp_bringup_ap

#### brings a second CPU online

- brings a second CPU online
   - Expected: ok is true
   - Expected: smp_online_count() equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("brings a second CPU online")
smp_init()
val ok = smp_bringup_ap(1u32)
expect(ok).to_equal(true)
expect(smp_online_count()).to_equal(2u32)
```

</details>

#### refuses to bring up cpu 0 (BSP is already online)

- refuses to bring up cpu 0 (BSP is already online)
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to bring up cpu 0 (BSP is already online)")
smp_init()
val ok = smp_bringup_ap(0u32)
expect(ok).to_equal(false)
```

</details>

#### refuses cpu_id >= MAX_CPUS

- refuses cpu_id >= MAX_CPUS
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses cpu_id >= MAX_CPUS")
smp_init()
val ok = smp_bringup_ap(MAX_CPUS)
expect(ok).to_equal(false)
```

</details>

### firmware APIC registration

#### records firmware APIC ids without marking APs online

- records firmware APIC ids without marking APs online
   - Expected: count equals `3u32`
   - Expected: smp_num_cpus() equals `3u32`
   - Expected: percpu_is_present(2u32) is true
   - Expected: percpu_apic_id(1u32).unwrap() equals `9u32`
   - Expected: percpu_is_online(1u32) is false
   - Expected: smp_online_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records firmware APIC ids without marking APs online")
smp_init()

val count = smp_register_firmware_apic_ids([4u32, 9u32, 13u32])

expect(count).to_equal(3u32)
expect(smp_num_cpus()).to_equal(3u32)
expect(percpu_is_present(2u32)).to_equal(true)
expect(percpu_apic_id(1u32).unwrap()).to_equal(9u32)
expect(percpu_is_online(1u32)).to_equal(false)
expect(smp_online_count()).to_equal(1u32)
```

</details>

#### tracks AP startup and marks online by APIC id

- tracks AP startup and marks online by APIC id
   - Expected: smp_mark_ap_startup_sent(1u32) is true
   - Expected: smp_ap_startup_sent(1u32) is true
   - Expected: smp_mark_ap_started_by_apic_id(13u32) is true
   - Expected: percpu_is_online(2u32) is true
   - Expected: smp_online_count() equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks AP startup and marks online by APIC id")
smp_init()
smp_register_firmware_apic_ids([4u32, 9u32, 13u32])

expect(smp_mark_ap_startup_sent(1u32)).to_equal(true)
expect(smp_ap_startup_sent(1u32)).to_equal(true)
expect(smp_mark_ap_started_by_apic_id(13u32)).to_equal(true)

expect(percpu_is_online(2u32)).to_equal(true)
expect(smp_online_count()).to_equal(2u32)
```

</details>

#### rejects unknown APIC ids

- rejects unknown APIC ids
   - Expected: smp_mark_ap_started_by_apic_id(99u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown APIC ids")
smp_init()
smp_register_firmware_apic_ids([4u32, 9u32])

expect(smp_mark_ap_started_by_apic_id(99u32)).to_equal(false)
```

</details>

#### reports when registered APs need automatic boot startup

- reports when registered APs need automatic boot startup
   - Expected: x86_registered_ap_boot_startup_needed() is false
   - Expected: x86_registered_ap_boot_startup_needed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports when registered APs need automatic boot startup")
smp_init()
expect(x86_registered_ap_boot_startup_needed()).to_equal(false)

smp_register_firmware_apic_ids([4u32, 9u32])

expect(x86_registered_ap_boot_startup_needed()).to_equal(true)
```

</details>

### smp IPIs
_IPI send/take and bitmask accumulation via g_percpu[].ipi_pending._

#### send/take round-trips the reason bitmask

- send/take round-trips the reason bitmask
   - Expected: sent is true
   - Expected: got equals `IPI_RESCHED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("send/take round-trips the reason bitmask")
smp_init()
smp_bringup_ap(1u32)
val sent = smp_send_ipi(1u32, IPI_RESCHED)
expect(sent).to_equal(true)
val got = smp_take_ipi(1u32)
expect(got).to_equal(IPI_RESCHED)
```

</details>

#### multiple IPIs OR into the pending mask

- multiple IPIs OR into the pending mask
   - Expected: got equals `combined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple IPIs OR into the pending mask")
smp_init()
smp_bringup_ap(1u32)
smp_send_ipi(1u32, IPI_RESCHED)
smp_send_ipi(1u32, IPI_TLB_FLUSH)
val got = smp_take_ipi(1u32)
val combined: u32 = IPI_RESCHED | IPI_TLB_FLUSH
expect(got).to_equal(combined)
```

</details>

#### take_ipi clears the pending mask

- take_ipi clears the pending mask
   - Expected: got2 equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("take_ipi clears the pending mask")
smp_init()
smp_bringup_ap(1u32)
smp_send_ipi(1u32, IPI_HALT)
smp_take_ipi(1u32)
val got2 = smp_take_ipi(1u32)
expect(got2).to_equal(0u32)
```

</details>

#### send_ipi to offline CPU returns false

- send_ipi to offline CPU returns false
   - Expected: sent is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("send_ipi to offline CPU returns false")
smp_init()
val sent = smp_send_ipi(5u32, IPI_RESCHED)
expect(sent).to_equal(false)
```

</details>

### preemption counter

#### disable nests and enable decrements

- disable nests and enable decrements
   - Expected: percpu_preempt_enabled(0u32) is true
   - Expected: percpu_preempt_enabled(0u32) is false
   - Expected: percpu_preempt_enabled(0u32) is false
   - Expected: percpu_preempt_enabled(0u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disable nests and enable decrements")
smp_init()
expect(percpu_preempt_enabled(0u32)).to_equal(true)
percpu_preempt_disable(0u32)
expect(percpu_preempt_enabled(0u32)).to_equal(false)
percpu_preempt_disable(0u32)
percpu_preempt_enable(0u32)
expect(percpu_preempt_enabled(0u32)).to_equal(false)
percpu_preempt_enable(0u32)
expect(percpu_preempt_enabled(0u32)).to_equal(true)
```

</details>

### IPI reason constants

#### have stable bit assignments

- have stable bit assignments
   - Expected: IPI_RESCHED equals `0x1u32`
   - Expected: IPI_TLB_FLUSH equals `0x2u32`
   - Expected: IPI_HALT equals `0x4u32`
   - Expected: IPI_CALL_FUNC equals `0x8u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("have stable bit assignments")
expect(IPI_RESCHED).to_equal(0x1u32)
expect(IPI_TLB_FLUSH).to_equal(0x2u32)
expect(IPI_HALT).to_equal(0x4u32)
expect(IPI_CALL_FUNC).to_equal(0x8u32)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e381b093ba567f144e4a01eeeb34befd325059be179dec8b456310f1a3bb72c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e381b093ba567f144e4a01eeeb34befd325059be179dec8b456310f1a3bb72c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e381b093ba567f144e4a01eeeb34befd325059be179dec8b456310f1a3bb72c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/smp/smp_spec.spl
mirror: doc/06_spec/unit/os/kernel/smp/smp_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/smp/smp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/smp/smp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/smp/smp_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BSP alone is online after init' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/smp/smp_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'brings a second CPU online' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/smp/smp_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses to bring up cpu 0 (BSP is already online)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
