# Multicore Green Fanout Stress Specification

> This perf stress spec keeps the Simple concurrency rows comparable: OS threads, cooperative green, and multicore green all run the same deterministic fanout workload and must produce the same checksum. The multicore-green row separately classifies runtime-pool use, work-stealing queue selection, and public counter evidence, so inline fallback or a single FIFO queue cannot be mistaken for Go-like M:N CPU-parallel evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Fanout Stress Specification

This perf stress spec keeps the Simple concurrency rows comparable: OS threads, cooperative green, and multicore green all run the same deterministic fanout workload and must produce the same checksum. The multicore-green row separately classifies runtime-pool use, work-stealing queue selection, and public counter evidence, so inline fallback or a single FIFO queue cannot be mistaken for Go-like M:N CPU-parallel evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-perf-fanout |
| Category | Performance / Concurrency |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/05_perf/stress/multicore_green_fanout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This perf stress spec keeps the Simple concurrency rows comparable: OS threads,
cooperative green, and multicore green all run the same deterministic fanout
workload and must produce the same checksum. The multicore-green row separately
classifies runtime-pool use, work-stealing queue selection, and public counter
evidence, so inline fallback or a single FIFO queue cannot be mistaken for
Go-like M:N CPU-parallel evidence.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### multicore green fanout stress

<details>
<summary>Advanced: matches OS-thread fanout/fanin checksum</summary>

#### matches OS-thread fanout/fanin checksum _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches OS-thread fanout/fanin checksum
- Write and run the OS-thread fanout probe through direct simple run
   - Expected: stderr equals ``
   - Expected: stdout.trim() equals ``
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("matches OS-thread fanout/fanin checksum")
step("Write and run the OS-thread fanout probe through direct simple run")
val probe_path = unique_probe_path("mcg_thread_fanout")
val (stdout, stderr, code) = run_probe(probe_path, thread_probe_source())
expect(stderr).to_equal("")
expect(stdout.trim()).to_equal("")
expect(code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: matches cooperative-green fanout checksum on the current carrier</summary>

#### matches cooperative-green fanout checksum on the current carrier _(slow)_

- matches cooperative-green fanout checksum on the current carrier
- Write and run the cooperative-green fanout probe through direct simple run
   - Expected: stderr equals ``
   - Expected: stdout.trim() equals ``
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("matches cooperative-green fanout checksum on the current carrier")
step("Write and run the cooperative-green fanout probe through direct simple run")
val probe_path = unique_probe_path("mcg_coop_fanout")
val (stdout, stderr, code) = run_probe(probe_path, cooperative_probe_source())
expect(stderr).to_equal("")
expect(stdout.trim()).to_equal("")
expect(code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: matches multicore-green fanout checksum and classifies M:N evidence</summary>

#### matches multicore-green fanout checksum and classifies M:N evidence _(slow)_

- matches multicore-green fanout checksum and classifies M:N evidence
- Prepare deterministic multicore-green fanout inputs
- Spawn eight multicore-green workers
- Count runtime-pool and inline-fallback evidence
- Join multicore-green workers and classify evidence
- Verify checksum and runtime evidence accounting
   - Expected: got equals `expected`
   - Expected: pool_used + inline_fallback equals `8`
- Verify the row is classified as counter-qualified M:N evidence, runtime-pool-only evidence, or explicit inline fallback
- Verify runtime-pool fanout uses work stealing and public counter deltas
   - Expected: queue_model equals `work_stealing`
   - Expected: submitted_delta equals `8`
   - Expected: completed_delta equals `8`
   - Expected: pending_count equals `0`
   - Expected: busy_count equals `0`
   - Expected: blocked_count equals `0`
- Verify runtime-pool fanout without the counter gate is not profile-grade counter evidence
   - Expected: queue_model equals `work_stealing`
   - Expected: pool_used equals `8`
   - Expected: inline_fallback equals `0`
   - Expected: submitted_delta equals `0`
   - Expected: completed_delta equals `0`
   - Expected: pending_count equals `0`
   - Expected: busy_count equals `0`
   - Expected: blocked_count equals `0`
- Verify inline fallback is not counted as M:N evidence
   - Expected: pool_used equals `0`
   - Expected: inline_fallback equals `8`
   - Expected: queue_model equals `inline_or_unavailable`
   - Expected: pending_count equals `0`
   - Expected: busy_count equals `0`
   - Expected: blocked_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 97 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("matches multicore-green fanout checksum and classifies M:N evidence")
step("Prepare deterministic multicore-green fanout inputs")
val iterations = 512
val expected = fanout_expected(8, iterations)
val counter_evidence_enabled = (rt_env_get("SIMPLE_MULTICORE_GREEN_COUNTER_EVIDENCE") ?? "") == "1"
var submitted_before = 0
var completed_before = 0
if counter_evidence_enabled:
    submitted_before = multicore_green_submitted_count()
    completed_before = multicore_green_completed_count()

step("Spawn eight multicore-green workers")
val h0 = multicore_green_spawn(\: fanout_work(0, iterations))
val h1 = multicore_green_spawn(\: fanout_work(1, iterations))
val h2 = multicore_green_spawn(\: fanout_work(2, iterations))
val h3 = multicore_green_spawn(\: fanout_work(3, iterations))
val h4 = multicore_green_spawn(\: fanout_work(4, iterations))
val h5 = multicore_green_spawn(\: fanout_work(5, iterations))
val h6 = multicore_green_spawn(\: fanout_work(6, iterations))
val h7 = multicore_green_spawn(\: fanout_work(7, iterations))

var pool_used = 0
var inline_fallback = 0
step("Count runtime-pool and inline-fallback evidence")
if h0.used_runtime_pool(): pool_used = pool_used + 1
if h1.used_runtime_pool(): pool_used = pool_used + 1
if h2.used_runtime_pool(): pool_used = pool_used + 1
if h3.used_runtime_pool(): pool_used = pool_used + 1
if h4.used_runtime_pool(): pool_used = pool_used + 1
if h5.used_runtime_pool(): pool_used = pool_used + 1
if h6.used_runtime_pool(): pool_used = pool_used + 1
if h7.used_runtime_pool(): pool_used = pool_used + 1
if h0.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h1.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h2.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h3.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h4.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h5.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h6.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h7.ran_inline_fallback(): inline_fallback = inline_fallback + 1

step("Join multicore-green workers and classify evidence")
val got = h0.join() + h1.join() + h2.join() + h3.join() + h4.join() + h5.join() + h6.join() + h7.join()

val queue_model = multicore_queue_model()
var submitted_delta = 0
var completed_delta = 0
var pending_count = 0
var busy_count = 0
var blocked_count = 0
if counter_evidence_enabled:
    submitted_delta = multicore_green_submitted_count() - submitted_before
    completed_delta = multicore_green_completed_count() - completed_before
    pending_count = multicore_green_pending_count()
    busy_count = multicore_green_busy_count()
    blocked_count = multicore_green_blocked_count()
val counters_quiesced = pending_count == 0 and busy_count == 0 and blocked_count == 0
val has_counter_evidence = submitted_delta == 8 and completed_delta == 8 and counters_quiesced
val has_counters_unavailable = submitted_delta == 0 and completed_delta == 0 and counters_quiesced
val has_mn_evidence = counter_evidence_enabled and pool_used == 8 and inline_fallback == 0 and queue_model == "work_stealing" and has_counter_evidence
val has_runtime_pool_without_counters = not counter_evidence_enabled and pool_used == 8 and inline_fallback == 0 and queue_model == "work_stealing" and has_counters_unavailable
val has_inline_fallback_only = pool_used == 0 and inline_fallback == 8 and queue_model == "inline_or_unavailable" and counters_quiesced
val evidence_class = if has_mn_evidence: 3 elif has_runtime_pool_without_counters: 2 elif has_inline_fallback_only: 1 else: 0

step("Verify checksum and runtime evidence accounting")
expect(got).to_equal(expected)
expect(pool_used + inline_fallback).to_equal(8)
step("Verify the row is classified as counter-qualified M:N evidence, runtime-pool-only evidence, or explicit inline fallback")
expect(evidence_class).to_be_greater_than(0)
if has_mn_evidence:
    step("Verify runtime-pool fanout uses work stealing and public counter deltas")
    expect(queue_model).to_equal("work_stealing")
    expect(submitted_delta).to_equal(8)
    expect(completed_delta).to_equal(8)
    expect(pending_count).to_equal(0)
    expect(busy_count).to_equal(0)
    expect(blocked_count).to_equal(0)
elif has_runtime_pool_without_counters:
    step("Verify runtime-pool fanout without the counter gate is not profile-grade counter evidence")
    expect(queue_model).to_equal("work_stealing")
    expect(pool_used).to_equal(8)
    expect(inline_fallback).to_equal(0)
    expect(counter_evidence_enabled).to_be(false)
    expect(submitted_delta).to_equal(0)
    expect(completed_delta).to_equal(0)
    expect(pending_count).to_equal(0)
    expect(busy_count).to_equal(0)
    expect(blocked_count).to_equal(0)
else:
    step("Verify inline fallback is not counted as M:N evidence")
    expect(pool_used).to_equal(0)
    expect(inline_fallback).to_equal(8)
    expect(queue_model).to_equal("inline_or_unavailable")
    expect(pending_count).to_equal(0)
    expect(busy_count).to_equal(0)
    expect(blocked_count).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Research:** `doc/01_research/local/multicore_green.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78f55257c6d25062427b92708f33febe9b5084a39090840937f5cc88689a6843`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78f55257c6d25062427b92708f33febe9b5084a39090840937f5cc88689a6843`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78f55257c6d25062427b92708f33febe9b5084a39090840937f5cc88689a6843`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/stress/multicore_green_fanout_spec.spl
mirror: doc/06_spec/05_perf/stress/multicore_green_fanout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/stress/multicore_green_fanout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/stress/multicore_green_fanout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/stress/multicore_green_fanout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/stress/multicore_green_fanout_spec.spl:211:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches OS-thread fanout/fanin checksum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/stress/multicore_green_fanout_spec.spl:221:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches cooperative-green fanout checksum on the current carrier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/stress/multicore_green_fanout_spec.spl:231:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches multicore-green fanout checksum and classifies M:N evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
