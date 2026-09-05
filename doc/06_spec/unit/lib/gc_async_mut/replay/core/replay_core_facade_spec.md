# Replay Core Facade Specification

> Tests covering gc_async_mut replay core facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Core Facade Specification

## Scenarios

### gc_async_mut replay core facades

#### re-exports event kind and event records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports event kind and event records
   - Expected: event.kind.to_i32() equals `2`
   - Expected: ReplayEventKind.from_i32(2).to_text() equals `Step`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports event kind and event records")
val event = ReplayEvent(
    seq_id: 1,
    kind: ReplayEventKind.Step,
    timestamp: 2,
    file_hash: 3,
    line: 4,
    name_hash: 5,
    value_a: 6,
    value_b: 7
)

expect(event.kind.to_i32()).to_equal(2)
expect(ReplayEventKind.from_i32(2).to_text()).to_equal("Step")
```

</details>

#### re-exports replay engine and no-op hook

- re-exports replay engine and no-op hook
   - Expected: engine.events.len() equals `1`
   - Expected: engine.is_recording() is true
   - Expected: hook.is_off() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports replay engine and no-op hook")
var engine = ReplayEngine.create("record")
engine.on_step("main.spl", 12, 1)
val hook = NoopReplayHook()

expect(engine.events.len()).to_equal(1)
expect(engine.is_recording()).to_equal(true)
expect(hook.is_off()).to_equal(true)
```

</details>

#### re-exports global engine helpers

- re-exports global engine helpers
   - Expected: active.is_some() is true
   - Expected: replay_get() equals `None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports global engine helpers")
replay_init("record")
val active = replay_get()
replay_shutdown()

expect(active.is_some()).to_equal(true)
expect(replay_get()).to_equal(None)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut replay core facades.
- gc_async_mut replay core facades

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26cd13a0335e1c16e2822c7663e4b68fdf9bb9f47732ebcd473a97b4405acb4e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26cd13a0335e1c16e2822c7663e4b68fdf9bb9f47732ebcd473a97b4405acb4e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26cd13a0335e1c16e2822c7663e4b68fdf9bb9f47732ebcd473a97b4405acb4e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports event kind and event records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports replay engine and no-op hook' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports global engine helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
