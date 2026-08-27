# Replay Offmode Overhead Specification

> Tests covering SReplay Track 2.10 — off-mode overhead.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Offmode Overhead Specification

## Scenarios

### SReplay Track 2.10 — off-mode overhead

#### replay_hook_schedule 1000 calls in Off mode completes <100ms

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replay_hook_schedule 1000 calls in Off mode completes <100ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replay_hook_schedule 1000 calls in Off mode completes <100ms")
val ms = _bench_schedule()
expect(ms).to_be_less_than(100)
```

</details>

#### replay_hook_syscall_enter 1000 calls in Off mode completes <100ms

- replay_hook_syscall_enter 1000 calls in Off mode completes <100ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replay_hook_syscall_enter 1000 calls in Off mode completes <100ms")
val ms = _bench_syscall_enter()
expect(ms).to_be_less_than(100)
```

</details>

#### replay_hook_irq 1000 calls in Off mode completes <100ms

- replay_hook_irq 1000 calls in Off mode completes <100ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replay_hook_irq 1000 calls in Off mode completes <100ms")
val ms = _bench_irq()
expect(ms).to_be_less_than(100)
```

</details>

#### replay_hook_timer_read 1000 calls in Off mode returns quickly <100ms

- replay_hook_timer_read 1000 calls in Off mode returns quickly <100ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replay_hook_timer_read 1000 calls in Off mode returns quickly <100ms")
val ms = _bench_timer_read()
expect(ms).to_be_less_than(100)
```

</details>

#### mode is Off after explicit init

- mode is Off after explicit init
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mode is Off after explicit init")
val ok = _mode_off_after_init()
expect(ok).to_equal(true)
```

</details>

#### Off -> Record -> Off leaves no residual overhead (<100ms)

- Off -> Record -> Off leaves no residual overhead (<100ms)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Off -> Record -> Off leaves no residual overhead (<100ms)")
val ms = _bench_off_record_off()
expect(ms).to_be_less_than(100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_offmode_overhead_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SReplay Track 2.10 — off-mode overhead.
- SReplay Track 2.10 — off-mode overhead

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9750bd6c1e93300caffa5b929a06a76e939fc33e1d629e2feb00ef944c785234`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9750bd6c1e93300caffa5b929a06a76e939fc33e1d629e2feb00ef944c785234`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9750bd6c1e93300caffa5b929a06a76e939fc33e1d629e2feb00ef944c785234`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/replay_offmode_overhead_spec.spl
mirror: doc/06_spec/03_system/tools/replay_offmode_overhead_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/replay_offmode_overhead_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/replay_offmode_overhead_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/replay_offmode_overhead_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replay_hook_schedule 1000 calls in Off mode completes <100ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_offmode_overhead_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replay_hook_syscall_enter 1000 calls in Off mode completes <100ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_offmode_overhead_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replay_hook_irq 1000 calls in Off mode completes <100ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
