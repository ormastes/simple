# os_log_modes_spec

> Purpose: This spec proves os log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# os_log_modes_spec

Purpose: This spec proves os log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/os_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves os log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### os log mode CLI options

#### reports the focused compiler version without entering OS parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the focused compiler version without entering OS parsing
   - Expected: code equals `0`
   - Expected: out equals `simple-bootstrap 1.0.0-RC\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OSLOGMODES-001
step("reports the focused compiler version without entering OS parsing")
val (out, err, code) = _run_os(["--version"])
expect(code).to_equal(0)
expect(out).to_equal("simple-bootstrap 1.0.0-RC\n")
```

</details>

#### shows shared log options in help

- shows shared log options in help
- shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows shared log options in help")
step("shows shared log options in help")
val (out, err, code) = _run_os(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for usage output

- supports log-mode json for usage output
- supports log-mode json for usage output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json for usage output")
step("supports log-mode json for usage output")
val (out, err, code) = _run_os(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"os\"")
expect(out).to_contain("\"status\":\"usage\"")
```

</details>

#### supports dot progress for usage output

- supports dot progress for usage output
- supports dot progress for usage output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress for usage output")
step("supports dot progress for usage output")
val (out, err, code) = _run_os(["--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("SimpleOS")
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
val (out, err, code) = _run_os(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### emits json for deterministic targets output

- emits json for deterministic targets output
- emits json for deterministic targets output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits json for deterministic targets output")
step("emits json for deterministic targets output")
val (out, err, code) = _run_os(["--log-mode=json", "targets"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"os\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain("\"action\":\"targets\"")
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
- `REQ-OSLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3296d0d46afd273f20d463aa25b0d951d005de7c73b93f595d70fd570856d2c7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3296d0d46afd273f20d463aa25b0d951d005de7c73b93f595d70fd570856d2c7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3296d0d46afd273f20d463aa25b0d951d005de7c73b93f595d70fd570856d2c7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/os_log_modes_spec.spl
mirror: doc/06_spec/02_integration/app/os_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/os_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/os_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/os_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/os_log_modes_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the focused compiler version without entering OS parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/os_log_modes_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/os_log_modes_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json for usage output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
