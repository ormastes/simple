# Replay Test Runner Adapter Specification

> Tests covering TestRunnerReplayAdapter, TestReplayMode, TestRunnerReplayAdapter lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Test Runner Adapter Specification

## Scenarios

### TestRunnerReplayAdapter

### TestReplayMode

#### Off mode to_text returns off

- Off mode to_text returns off
   - Expected: m.to_text() equals `off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Off mode to_text returns off")
val m = TestReplayMode::Off
expect(m.to_text()).to_equal("off")
```

</details>

#### RecordOnFail mode to_text returns record_on_fail

- RecordOnFail mode to_text returns record_on_fail
   - Expected: m.to_text() equals `record_on_fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RecordOnFail mode to_text returns record_on_fail")
val m = TestReplayMode::RecordOnFail
expect(m.to_text()).to_equal("record_on_fail")
```

</details>

### TestRunnerReplayAdapter lifecycle

#### create stores mode and trace_dir

- create stores mode and trace_dir
   - Expected: adapter.mode.to_text() equals `off`
   - Expected: adapter.trace_dir equals `/tmp/traces`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("create stores mode and trace_dir")
val adapter = TestRunnerReplayAdapter::create(TestReplayMode::Off, "/tmp/traces")
expect(adapter.mode.to_text()).to_equal("off")
expect(adapter.trace_dir).to_equal("/tmp/traces")
```

</details>

#### list_recorded_traces returns empty on fresh adapter

- list_recorded_traces returns empty on fresh adapter
   - Expected: traces.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("list_recorded_traces returns empty on fresh adapter")
val adapter = TestRunnerReplayAdapter::create(TestReplayMode::Off, "/tmp/traces")
val traces = adapter.list_recorded_traces()
expect(traces.len()).to_equal(0)
```

</details>

#### get_trace_dir field returns configured path

- get_trace_dir field returns configured path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_trace_dir field returns configured path")
val adapter = TestRunnerReplayAdapter::create(TestReplayMode::RecordOnFail, "/tmp/replay_traces")
expect(adapter.trace_dir).to_start_with("/tmp")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_test_runner_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestRunnerReplayAdapter, TestReplayMode, TestRunnerReplayAdapter lifecycle.
- TestRunnerReplayAdapter
- TestReplayMode
- TestRunnerReplayAdapter lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `f5860a4f3543ca906200efbd22c6b70691df95dc6d240957b4969821c4e07e1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5860a4f3543ca906200efbd22c6b70691df95dc6d240957b4969821c4e07e1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5860a4f3543ca906200efbd22c6b70691df95dc6d240957b4969821c4e07e1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/replay_test_runner_adapter_spec.spl
mirror: doc/06_spec/03_system/tools/replay_test_runner_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/replay_test_runner_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/replay_test_runner_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/replay_test_runner_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/replay_test_runner_adapter_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Off mode to_text returns off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_test_runner_adapter_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RecordOnFail mode to_text returns record_on_fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_test_runner_adapter_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create stores mode and trace_dir' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
