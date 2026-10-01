# Replay Container Facade Specification

> Tests covering nogc_async_mut replay container facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Container Facade Specification

## Scenarios

### nogc_async_mut replay container facades

#### re-exports checkpoint format records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports checkpoint format records
   - Expected: cp.process_count() equals `1`
   - Expected: cp.total_pages() equals `1`
   - Expected: decoded.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports checkpoint format records")
var proc = ProcessSnapshot.create(42)
proc.add_register(7)
proc.add_page(DirtyPage(address: 4096, size: 4096, data_offset: 0))
proc.add_fd(FdEntry(fd: 1, path: "/tmp/out", offset: 0, flags: 0))
var cp = ContainerCheckpoint.create(3, 99)
cp.add_process(proc)
val encoded = encode_checkpoint(cp)
val decoded = decode_checkpoint(encoded)

expect(cp.process_count()).to_equal(1)
expect(cp.total_pages()).to_equal(1)
expect(encoded.len()).to_be_greater_than(0)
expect(decoded.is_ok()).to_equal(true)
```

</details>

#### re-exports container replay driver

- re-exports container replay driver
   - Expected: saved.is_ok() is true
   - Expected: driver.checkpoint_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports container replay driver")
var driver = ContainerReplayDriver.create("record", "container1")
val saved = driver.save_checkpoint(1)
driver.advance_event()

expect(saved.is_ok()).to_equal(true)
expect(driver.checkpoint_count()).to_equal(1)
expect(driver.info()).to_contain("container1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut replay container facades.
- nogc_async_mut replay container facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `20889fa95b99d78af0f2d5e77c7245a21ea33629d5cdb817fc9f02a794fa84d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20889fa95b99d78af0f2d5e77c7245a21ea33629d5cdb817fc9f02a794fa84d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20889fa95b99d78af0f2d5e77c7245a21ea33629d5cdb817fc9f02a794fa84d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports checkpoint format records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports container replay driver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
