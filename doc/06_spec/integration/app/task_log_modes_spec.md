# task_log_modes_spec

> Purpose: This spec proves task log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# task_log_modes_spec

Purpose: This spec proves task log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/task_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves task log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### task log mode CLI options

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
# @req: REQ-TASKLOGMODES-001
step("shows shared log options in help")
val (out, err, code) = _run_task(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Task")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

- supports log-mode json ready output
- supports log-mode json ready output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json ready output")
step("supports log-mode json ready output")
val (out, err, code) = _run_task(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"task\"")
expect(out).to_contain("\"status\":\"ready\"")
expect(out).to_contain("\"codex\"")
```

</details>

#### supports json driver listing

- supports json driver listing
- supports json driver listing
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports json driver listing")
step("supports json driver listing")
val (out, err, code) = _run_task(["--log-mode=json", "--list"])
expect(code).to_equal(0)
expect(out).to_contain("\"drivers\"")
expect(out).to_contain("\"claude\"")
```

</details>

#### supports json planned dispatch output

- supports json planned dispatch output
- supports json planned dispatch output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports json planned dispatch output")
step("supports json planned dispatch output")
val (out, err, code) = _run_task(["--log-mode=json", "codex", "write tests"])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"driver\":\"codex\"")
expect(out).to_contain("\"description\":\"write tests\"")
```

</details>

#### supports dot progress for help output

- supports dot progress for help output
- supports dot progress for help output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress for help output")
step("supports dot progress for help output")
val (out, err, code) = _run_task(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple Task")
expect(out).to_contain("Simple Task")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("rejects invalid log mode")
val (out, err, code) = _run_task(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json missing description output

- renders json missing description output
- renders json missing description output
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders json missing description output")
step("renders json missing description output")
val (out, err, code) = _run_task(["--log-mode=json", "codex"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Task description required for codex")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-TASKLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a32cfc66fe860d57591bb3c4dfc0bab9fe2d993673955cb1ef607a775d0e34b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a32cfc66fe860d57591bb3c4dfc0bab9fe2d993673955cb1ef607a775d0e34b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a32cfc66fe860d57591bb3c4dfc0bab9fe2d993673955cb1ef607a775d0e34b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/task_log_modes_spec.spl
mirror: doc/06_spec/integration/app/task_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/task_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/task_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/task_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/task_log_modes_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/task_log_modes_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json ready output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/task_log_modes_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports json driver listing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
