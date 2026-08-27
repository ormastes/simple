# Engine Core Facade Specification

> Tests covering gc_async_mut engine core facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Core Facade Specification

## Scenarios

### gc_async_mut engine core facade

#### re-exports clock, console, pool, and coroutine helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports clock, console, pool, and coroutine helpers
   - Expected: frame.frame_count equals `2`
   - Expected: console.has_command("ping") is true
   - Expected: pool.acquire("enemy") equals `0`
   - Expected: pool.count() equals `1`
   - Expected: timer.tick(0.6) is true
   - Expected: frames.tick() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports clock, console, pool, and coroutine helpers")
var clock = Clock.create(Seconds(value: 0.016))
clock.tick(1000000000)
val frame = clock.tick(1016000000)
expect(frame.frame_count).to_equal(2)
expect(frame.delta.value).to_be_greater_than(0.015)

var console = GameConsole.new(4)
console.register_command("ping", "Pong")
expect(console.has_command("ping")).to_equal(true)

var pool = ObjectPool.new(2)
expect(pool.acquire("enemy")).to_equal(0)
expect(pool.count()).to_equal(1)

var timer = WaitTimer.wait_seconds(0.5)
expect(timer.tick(0.6)).to_equal(true)
var frames = FrameCounter.wait_frames(1)
expect(frames.tick()).to_equal(true)
```

</details>

#### re-exports profiler records

- re-exports profiler records
   - Expected: sample.duration_ms() equals `3.0`
   - Expected: profiler.sample_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports profiler records")
val sample = ProfileSample(name: "tick", start_ms: 1.0, end_ms: 4.0, depth: 0)
expect(sample.duration_ms()).to_equal(3.0)
var profiler = Profiler.new(8)
profiler.begin_scope("update", 0.0)
profiler.end_scope(2.0)
expect(profiler.sample_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine core facade.
- gc_async_mut engine core facade

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aaf66740fd520a49b2209f9f8d3b3b9ad588c0271b50750ea72f5e6832a4d129`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aaf66740fd520a49b2209f9f8d3b3b9ad588c0271b50750ea72f5e6832a4d129`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aaf66740fd520a49b2209f9f8d3b3b9ad588c0271b50750ea72f5e6832a4d129`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports clock, console, pool, and coroutine helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports profiler records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
