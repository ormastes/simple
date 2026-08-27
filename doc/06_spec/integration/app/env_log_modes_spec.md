# env_log_modes_spec

> Purpose: This spec proves env log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# env_log_modes_spec

Purpose: This spec proves env log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/env_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves env log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### env log mode CLI options

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
# @req: REQ-ENVLOGMODES-001
step("shows shared log options in help")
_setup_fixture()
val (out, err, code) = _run_env(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports create log-mode json

- supports create log-mode json
- supports create log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports create log-mode json")
step("supports create log-mode json")
_setup_fixture()
val (out, err, code) = _run_env(["create", "--name=test-env", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"create\"")
expect(out).to_contain("\"name\":\"test-env\"")
```

</details>

#### supports status log-mode json

- supports status log-mode json
- supports status log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports status log-mode json")
step("supports status log-mode json")
_setup_fixture()
val (_create_out, _create_err, _create_code) = _run_env(["create", "--name=test-env"])
val (out, err, code) = _run_env(["status", "--name=test-env", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"status\"")
expect(out).to_contain("\"exists\":true")
```

</details>

#### supports delete log-mode json

- supports delete log-mode json
- supports delete log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports delete log-mode json")
step("supports delete log-mode json")
_setup_fixture()
val (_create_out, _create_err, _create_code) = _run_env(["create", "--name=test-env"])
val (out, err, code) = _run_env(["delete", "--name=test-env", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"delete\"")
expect(out).to_contain("\"name\":\"test-env\"")
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
val (out, err, code) = _run_env(["status", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("No virtual environment found.")
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
val (out, err, code) = _run_env(["status", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-ENVLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3031e4db0635d6a233bb3b46b2309efaf1735da4f5a62f227370c16ab7083b28`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3031e4db0635d6a233bb3b46b2309efaf1735da4f5a62f227370c16ab7083b28`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3031e4db0635d6a233bb3b46b2309efaf1735da4f5a62f227370c16ab7083b28`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/env_log_modes_spec.spl
mirror: doc/06_spec/integration/app/env_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/env_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/env_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/env_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/env_log_modes_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/env_log_modes_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports create log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/env_log_modes_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports status log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
