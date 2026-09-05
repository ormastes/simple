# info_log_modes_spec

> Purpose: This spec proves info log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# info_log_modes_spec

Purpose: This spec proves info log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/info_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves info log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### info log mode CLI options

#### shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-INFOLOGMODES-001
step("shows shared log options in help")
_setup_fixture()
val (out, err, code) = _run_info(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports project log-mode json

- supports project log-mode json
- supports project log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports project log-mode json")
step("supports project log-mode json")
_setup_fixture()
val (out, err, code) = _run_info(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"info\"")
expect(out).to_contain("\"kind\":\"project\"")
expect(out).to_contain("\"name\":\"sample-info\"")
```

</details>

#### supports package log-mode json

- supports package log-mode json
- supports package log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports package log-mode json")
step("supports package log-mode json")
_setup_fixture()
val (out, err, code) = _run_info(["sample-pkg", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"kind\":\"package\"")
expect(out).to_contain("\"name\":\"sample-pkg\"")
```

</details>

#### supports dot progress

- supports dot progress
- supports dot progress
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress")
step("supports dot progress")
_setup_fixture()
val (out, err, code) = _run_info(["--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Project Info")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("rejects invalid log mode")
_setup_fixture()
val (out, err, code) = _run_info(["--log-mode=noisy"])
expect(code).to_equal(1)
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
- `REQ-INFOLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a62cf44efb9465bf585d07b4cef1feff81bb63f574e15e221279f02f00522a4e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a62cf44efb9465bf585d07b4cef1feff81bb63f574e15e221279f02f00522a4e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a62cf44efb9465bf585d07b4cef1feff81bb63f574e15e221279f02f00522a4e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/info_log_modes_spec.spl
mirror: doc/06_spec/integration/app/info_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/info_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/info_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/info_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/info_log_modes_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/info_log_modes_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports project log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/info_log_modes_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports package log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
