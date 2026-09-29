# Replay Adapters Facade Specification

> Tests covering gc_async_mut replay adapter facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Adapters Facade Specification

## Scenarios

### gc_async_mut replay adapter facades

#### re-exports interpreter and JIT adapters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports interpreter and JIT adapters
   - Expected: InterpreterReplayEventKind.Step.to_i32() equals `0`
   - Expected: interp.event_count() equals `1`
   - Expected: jit.event_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports interpreter and JIT adapters")
var interp = InterpreterReplayAdapter.create("record")
interp.wrap_step()

var jit = JitReplayAdapter.create(JitReplayMode.Record, "/tmp/simple-jit-replay")
jit.on_jit_compile("main", "module")

expect(InterpreterReplayEventKind.Step.to_i32()).to_equal(0)
expect(interp.event_count()).to_equal(1)
expect(jit.event_count()).to_equal(1)
```

</details>

#### re-exports remote and test runner adapters

- re-exports remote and test runner adapters
   - Expected: remote.event_count() equals `1`
   - Expected: runner.list_recorded_traces().len() equals `1`
   - Expected: TestReplayMode.from_text("replay").to_text() equals `replay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports remote and test runner adapters")
var remote = RemoteReplayAdapter.create(RemoteReplayMode.Record)
remote.on_register_read("pc", 12)

var runner = TestRunnerReplayAdapter.create(TestReplayMode.RecordAlways, "/tmp/simple-test-replay")
runner.wrap_test_execution("sample_spec.spl", "default")

expect(remote.event_count()).to_equal(1)
expect(runner.list_recorded_traces().len()).to_equal(1)
expect(TestReplayMode.from_text("replay").to_text()).to_equal("replay")
```

</details>

#### re-exports hosted execution and QEMU adapter constructors

- re-exports hosted execution and QEMU adapter constructors
   - Expected: hook.recording is false
   - Expected: qemu.status() equals `off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports hosted execution and QEMU adapter constructors")
val hook = ExecutionReplayHook.create("/tmp/simple-exec-replay")
val qemu = QemuReplayAdapter.create_from_backend("/tmp/qmp.sock", 1234)

expect(hook.recording).to_equal(false)
expect(qemu.status()).to_equal("off")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut replay adapter facades.
- gc_async_mut replay adapter facades

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `23f113429e053dba0b52bc9d28da6b042569f38c1a71c834f51dfb827f554bba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23f113429e053dba0b52bc9d28da6b042569f38c1a71c834f51dfb827f554bba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23f113429e053dba0b52bc9d28da6b042569f38c1a71c834f51dfb827f554bba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports interpreter and JIT adapters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports remote and test runner adapters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports hosted execution and QEMU adapter constructors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
