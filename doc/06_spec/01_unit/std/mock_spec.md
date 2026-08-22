# mock_spec

> Verifies the mock behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mock_spec

Verifies the mock behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the mock behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Mock Library (std twin smoke test)

#### creates a mock, stubs it, and verifies the call was recorded

- Verify: creates a mock, stubs it, and verifies the call was recorded


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK-001
step("Verify: creates a mock, stubs it, and verifies the call was recorded")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m = Mock.new("Service")
m.when("get").returns(42)
expect m.call("get", []) == 42
m.verify("get").was_called().verify()
expect m.recorder.call_count("get") == 1
```

</details>

#### creates a spy and records calls

- Verify: creates a spy and records calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK-001
step("Verify: creates a spy and records calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val s = Spy.new("Service")
s.record_call("ping", [])
expect s.was_called("ping") == true
```

</details>

#### creates a stub and stores values

- Verify: creates a stub and stores values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK-001
step("Verify: creates a stub and stores values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val s = Stub.new("Config").set("k", 1)
expect s.get("k") == 1
```

</details>

#### records and verifies via CallRecorder/CallVerifier directly

- Verify: records and verifies via CallRecorder/CallVerifier directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK-001
step("Verify: records and verifies via CallRecorder/CallVerifier directly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var recorder = CallRecorder.new()
recorder = recorder.record("m", [])
val verifier = CallVerifier.new(recorder, "m")
expect verifier.get_matching_calls().len() == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45fa49ea85245ab92cf847245607b07d5a4fd707fc6fc3921d05d51d8a7f9a2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45fa49ea85245ab92cf847245607b07d5a4fd707fc6fc3921d05d51d8a7f9a2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45fa49ea85245ab92cf847245607b07d5a4fd707fc6fc3921d05d51d8a7f9a2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/mock_spec.spl
mirror: doc/06_spec/01_unit/std/mock_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/mock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
