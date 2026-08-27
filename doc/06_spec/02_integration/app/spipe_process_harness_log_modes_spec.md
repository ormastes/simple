# spipe_process_harness_log_modes_spec

> Purpose: routes product file and directory access through semantic facades

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spipe_process_harness_log_modes_spec

Purpose: routes product file and directory access through semantic facades

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/spipe_process_harness_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: routes product file and directory access through semantic facades
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### spipe-process-harness log mode CLI options

#### routes product file and directory access through semantic facades

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes product file and directory access through semantic facades
- Verify: routes product file and directory access through semantic facades
   - Expected: source does not contain `extern fn rt_file_read_text`
   - Expected: source does not contain `extern fn rt_dir_create`
   - Expected: source does not contain `rt_file_read_text(`
   - Expected: source does not contain `rt_dir_create(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes product file and directory access through semantic facades")
step("Verify: routes product file and directory access through semantic facades")
# @req: REQ-APP-SpipProcHarnLogMode-001
val source = file_read_text("src/app/spipe_process_harness/main.spl")
expect(source.contains("extern fn rt_file_read_text")).to_equal(false)
expect(source.contains("extern fn rt_dir_create")).to_equal(false)
expect(source.contains("rt_file_read_text(")).to_equal(false)
expect(source.contains("rt_dir_create(")).to_equal(false)
```

</details>

#### shows shared log options in help

- shows shared log options in help
- Verify: shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows shared log options in help")
step("Verify: shows shared log options in help")
# @req: REQ-APP-SpipProcHarnLogMode-001
_setup_fixture()
val (out, err, code) = _run_harness(["--help"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for state

- supports log-mode json for state
- Verify: supports log-mode json for state
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json for state")
step("Verify: supports log-mode json for state")
# @req: REQ-APP-SpipProcHarnLogMode-001
_setup_fixture()
val (out, err, code) = _run_harness(["--log-mode=json", "state", "--feature", "sample", "--approved"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract
expect(out).to_contain("\"command\":\"spipe-process-harness state\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain(".spipe/sample/state.md")
```

</details>

#### supports dot progress for state

- supports dot progress for state
- Verify: supports dot progress for state
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress for state")
step("Verify: supports dot progress for state")
# @req: REQ-APP-SpipProcHarnLogMode-001
_setup_fixture()
val (out, err, code) = _run_harness(["--progress=dot", "state", "--feature", "sample", "--approved"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract
expect(out).to_contain(".")
expect(out).to_contain(".spipe/sample/state.md")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- Verify: rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("Verify: rejects invalid log mode")
# @req: REQ-APP-SpipProcHarnLogMode-001
_setup_fixture()
val (out, err, code) = _run_harness(["--log-mode=noisy", "state"])
expect(code).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-APP-SpipProcHarnLogMode-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7deeefbaba750af90dd0e5ed0159f88e45d26329547f68a59ee5e1b02c2bf2ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7deeefbaba750af90dd0e5ed0159f88e45d26329547f68a59ee5e1b02c2bf2ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7deeefbaba750af90dd0e5ed0159f88e45d26329547f68a59ee5e1b02c2bf2ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/app/spipe_process_harness_log_modes_spec.spl
mirror: doc/06_spec/02_integration/app/spipe_process_harness_log_modes_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/app/spipe_process_harness_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/spipe_process_harness_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/spipe_process_harness_log_modes_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/02_integration/app/spipe_process_harness_log_modes_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes product file and directory access through semantic facades' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/spipe_process_harness_log_modes_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/spipe_process_harness_log_modes_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json for state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
