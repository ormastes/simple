# Memory Leveling Device Adapters Specification

> Tests covering memory-leveling GPU and NIC adapters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Leveling Device Adapters Specification

## Scenarios

### memory-leveling GPU and NIC adapters

#### keeps a GPU queue pinned through submission and completion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a GPU queue pinned through submission and completion
   - Expected: manager.register_gpu_queue(301, 9, 4096, 0x8000).ok is true
   - Expected: manager.device_submit(301, 9).state equals `device_owned`
   - Expected: manager.release(301, 9).reason equals `protected`
   - Expected: manager.device_complete(301, 9).state equals `syncing_for_cpu`
   - Expected: manager.device_unmap(301, 9).state equals `cpu_owned`
   - Expected: manager.release(301, 9).reason equals `protected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps a GPU queue pinned through submission and completion")
var config = simpleos_memory_leveling_config_for_physical_capacity(4 * 1024 * 1024)
config.gpu_capacity_bytes = 65536
val manager = memory_leveling_manager_new(config)
expect(manager.register_gpu_queue(301, 9, 4096, 0x8000).ok).to_equal(true)
expect(manager.device_submit(301, 9).state).to_equal("device_owned")
expect(manager.release(301, 9).reason).to_equal("protected")
expect(manager.device_complete(301, 9).state).to_equal("syncing_for_cpu")
expect(manager.device_unmap(301, 9).state).to_equal("cpu_owned")
expect(manager.release(301, 9).reason).to_equal("protected")
```

</details>

#### tracks a temporary NIC buffer and rejects opaque migration

- tracks a temporary NIC buffer and rejects opaque migration
   - Expected: simpleos_memory_leveling_config_validate(config) equals `ok`
   - Expected: manager.register_nic_buffer(401, 10, 2048, 0xA000, true).ok is true
   - Expected: manager.device_submit(401, 10).ok is true
   - Expected: manager.device_complete(401, 10).ok is true
   - Expected: manager.device_unmap(401, 10).ok is true
   - Expected: manager.release(401, 10).ok is true
   - Expected: memory_leveling_device_migration_unavailable(401).reason equals `migration-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("tracks a temporary NIC buffer and rejects opaque migration")
var config = simpleos_memory_leveling_config_for_physical_capacity(4 * 1024 * 1024)
config.nic_capacity_bytes = 65536
config.nic_reserved_bytes = 0
expect(simpleos_memory_leveling_config_validate(config)).to_equal("ok")
val manager = memory_leveling_manager_new(config)
expect(manager.register_nic_buffer(401, 10, 2048, 0xA000, true).ok).to_equal(true)
expect(manager.device_submit(401, 10).ok).to_equal(true)
expect(manager.device_complete(401, 10).ok).to_equal(true)
expect(manager.device_unmap(401, 10).ok).to_equal(true)
expect(manager.release(401, 10).ok).to_equal(true)
expect(memory_leveling_device_migration_unavailable(401).reason).to_equal("migration-unavailable")
```

</details>

#### rolls back in-flight count when sync-for-cpu fails during completion

- rolls back in-flight count when sync-for-cpu fails during completion
   - Expected: manager.register_nic_buffer(402, 12, 4096, 0xB000, true).ok is true
   - Expected: manager.map_device(402, 12, MEMORY_DMA_DIRECTION_BIDIRECTIONAL, true).ok is true
   - Expected: manager.sync_for_device(402, 12).ok is true
   - Expected: manager.begin_in_flight(402, 12).ok is true
   - Expected: manager.begin_in_flight(402, 12).ok is true
   - Expected: completion.ok is false
   - Expected: completion.reason equals `in-flight`
   - Expected: allocation.in_flight_count equals `2`
   - Expected: completion.state equals `device_owned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rolls back in-flight count when sync-for-cpu fails during completion")
val config = simpleos_memory_leveling_config_for_physical_capacity(4 * 1024 * 1024)
val manager = memory_leveling_manager_new(config)
expect(manager.register_nic_buffer(402, 12, 4096, 0xB000, true).ok).to_equal(true)
expect(manager.map_device(402, 12, MEMORY_DMA_DIRECTION_BIDIRECTIONAL, true).ok).to_equal(true)
expect(manager.sync_for_device(402, 12).ok).to_equal(true)
expect(manager.begin_in_flight(402, 12).ok).to_equal(true)
expect(manager.begin_in_flight(402, 12).ok).to_equal(true)

val completion = manager.device_complete(402, 12)
expect(completion.ok).to_equal(false)
expect(completion.reason).to_equal("in-flight")
val allocation = manager.get(402).unwrap()
expect(allocation.in_flight_count).to_equal(2)
expect(completion.state).to_equal("device_owned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/memory_leveling_device_adapters_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering memory-leveling GPU and NIC adapters.
- memory-leveling GPU and NIC adapters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11d9a4616f559c2c2788c5f26b555e058da37074d5434af0288cc1f7f5da511a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11d9a4616f559c2c2788c5f26b555e058da37074d5434af0288cc1f7f5da511a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11d9a4616f559c2c2788c5f26b555e058da37074d5434af0288cc1f7f5da511a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/memory_leveling_device_adapters_spec.spl
mirror: doc/06_spec/01_unit/os/memory_leveling_device_adapters_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/memory_leveling_device_adapters_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/memory_leveling_device_adapters_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/memory_leveling_device_adapters_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/memory_leveling_device_adapters_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a GPU queue pinned through submission and completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/memory_leveling_device_adapters_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks a temporary NIC buffer and rejects opaque migration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/memory_leveling_device_adapters_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rolls back in-flight count when sync-for-cpu fails during completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
