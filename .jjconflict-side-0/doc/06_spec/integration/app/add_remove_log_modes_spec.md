# Add Remove Log Modes Specification

> Tests covering add/remove log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Add Remove Log Modes Specification

## Scenarios

### add/remove log mode CLI options

<details>
<summary>Advanced: shows shared add log options in help</summary>

#### shows shared add log options in help _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared add log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows shared add log options in help")
_setup_fixture()
val (out, err, code) = _run_app("add", ["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>


</details>

<details>
<summary>Advanced: shows shared remove log options in help</summary>

#### shows shared remove log options in help _(slow)_

- shows shared remove log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows shared remove log options in help")
_setup_fixture()
val (out, err, code) = _run_app("remove", ["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>


</details>

<details>
<summary>Advanced: supports add log-mode json</summary>

#### supports add log-mode json _(slow)_

- supports add log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports add log-mode json")
_setup_fixture()
val (out, err, code) = _run_app("add", ["beta@^1.0.0", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"add\"")
expect(out).to_contain("\"name\":\"beta\"")
expect(out).to_contain("\"constraint\":\"^1.0.0\"")
```

</details>


</details>

<details>
<summary>Advanced: supports remove log-mode json</summary>

#### supports remove log-mode json _(slow)_

- supports remove log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports remove log-mode json")
_setup_fixture()
val (out, err, code) = _run_app("remove", ["alpha", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"remove\"")
expect(out).to_contain("\"name\":\"alpha\"")
```

</details>


</details>

<details>
<summary>Advanced: supports add dot progress</summary>

#### supports add dot progress _(slow)_

- supports add dot progress
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports add dot progress")
_setup_fixture()
val (out, err, code) = _run_app("add", ["beta", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Added dependency 'beta'")
```

</details>


</details>

<details>
<summary>Advanced: supports remove dot progress</summary>

#### supports remove dot progress _(slow)_

- supports remove dot progress
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports remove dot progress")
_setup_fixture()
val (out, err, code) = _run_app("remove", ["alpha", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Removed dependency 'alpha'")
```

</details>


</details>

<details>
<summary>Advanced: rejects invalid add log mode</summary>

#### rejects invalid add log mode _(slow)_

- rejects invalid add log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid add log mode")
_setup_fixture()
val (out, err, code) = _run_app("add", ["beta", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: rejects invalid remove log mode</summary>

#### rejects invalid remove log mode _(slow)_

- rejects invalid remove log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid remove log mode")
_setup_fixture()
val (out, err, code) = _run_app("remove", ["alpha", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/add_remove_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering add/remove log mode CLI options.
- add/remove log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `626020e3eef03928e6f81e73d985dc4d04cc847b269d03875e7cea9bc3229018`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `626020e3eef03928e6f81e73d985dc4d04cc847b269d03875e7cea9bc3229018`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `626020e3eef03928e6f81e73d985dc4d04cc847b269d03875e7cea9bc3229018`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/add_remove_log_modes_spec.spl
mirror: doc/06_spec/integration/app/add_remove_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/add_remove_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/add_remove_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/add_remove_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/add_remove_log_modes_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared add log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/add_remove_log_modes_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared remove log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/add_remove_log_modes_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports add log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
