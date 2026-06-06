# SMP kernel scaffolding

> The SMP scaffold owns logical CPU discovery, AP startup bookkeeping, online CPU state, pending IPI masks, and the preemption disable counter used by scheduler and green-carrier wakeup paths. These tests exercise the interpreter-safe public API rather than importing private constants or mutating per-CPU globals directly.

<!-- sdn-diagram:id=smp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smp_spec -> std
smp_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

1. smp init

2. expect smp online count

3. expect percpu is online

4. expect percpu is online


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
expect smp_online_count().to_equal(1u32)
expect percpu_is_online(0u32).to_equal(true)
expect percpu_is_online(1u32).to_equal(false)
```

</details>

### smp_bringup_ap

#### brings a second CPU online

1. smp init

2. expect ok to equal

3. expect smp online count


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val ok = smp_bringup_ap(1u32)
expect ok.to_equal(true)
expect smp_online_count().to_equal(2u32)
```

</details>

#### refuses to bring up cpu 0 (BSP is already online)

1. smp init

2. expect ok to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val ok = smp_bringup_ap(0u32)
expect ok.to_equal(false)
```

</details>

#### refuses cpu_id >= MAX_CPUS

1. smp init

2. expect ok to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val ok = smp_bringup_ap(percpu_max_cpus())
expect ok.to_equal(false)
```

</details>

### firmware APIC registration

#### records firmware APIC ids without marking APs online

1. smp init

2. expect count to equal

3. expect smp num cpus

4. expect percpu is present

5. expect cpu apic id to equal

6. expect percpu is online

7. expect smp online count


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. smp init

2. smp register firmware apic ids

3. expect smp mark ap startup sent

4. expect smp ap startup sent

5. expect smp mark ap started by apic id

6. expect percpu is online

7. expect smp online count


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. smp init

2. smp register firmware apic ids

3. expect smp mark ap started by apic id


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_register_firmware_apic_ids([4u32, 9u32])

expect smp_mark_ap_started_by_apic_id(99u32).to_equal(false)
```

</details>

#### reports when registered APs need automatic boot startup

1. smp init

2. expect x86 registered ap boot startup needed

3. smp register firmware apic ids

4. expect x86 registered ap boot startup needed


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
expect x86_registered_ap_boot_startup_needed().to_equal(false)

smp_register_firmware_apic_ids([4u32, 9u32])

expect x86_registered_ap_boot_startup_needed().to_equal(true)
```

</details>

### smp IPIs
_IPI send/take and bitmask accumulation via g_percpu[].ipi_pending._

#### send/take round-trips the reason bitmask

1. smp init

2. smp bringup ap

3. expect sent to equal

4. expect got to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_bringup_ap(1u32)
val sent = smp_send_ipi(1u32, smp_ipi_resched())
expect sent.to_equal(true)
val got = smp_take_ipi(1u32)
expect got.to_equal(smp_ipi_resched())
```

</details>

#### multiple IPIs OR into the pending mask

1. smp init

2. smp bringup ap

3. smp send ipi

4. smp send ipi

5. expect got to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. smp init

2. smp bringup ap

3. smp send ipi

4. smp take ipi

5. expect got2 to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_bringup_ap(1u32)
smp_send_ipi(1u32, smp_ipi_halt())
smp_take_ipi(1u32)
val got2 = smp_take_ipi(1u32)
expect got2.to_equal(0u32)
```

</details>

#### send_ipi to offline CPU returns false

1. smp init

2. expect sent to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val sent = smp_send_ipi(5u32, smp_ipi_resched())
expect sent.to_equal(false)
```

</details>

### preemption counter

#### disable nests and enable decrements

1. smp init

2. expect percpu preempt enabled

3. percpu preempt disable

4. expect percpu preempt enabled

5. percpu preempt disable

6. percpu preempt enable

7. expect percpu preempt enabled

8. percpu preempt enable

9. expect percpu preempt enabled


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect smp ipi resched

2. expect smp ipi tlb flush

3. expect smp ipi halt

4. expect smp ipi call func


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
