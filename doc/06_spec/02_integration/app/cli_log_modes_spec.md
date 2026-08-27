# cli_log_modes_spec

> Purpose: This spec proves cli log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cli_log_modes_spec

Purpose: This spec proves cli log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/cli_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves cli log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### cli log mode CLI options

#### shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CLILOGMODES-001
step("shows shared log options in help")
val (out, err, code) = _run_cli(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Language")
expect(out).to_contain("Shared log options")
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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json ready output")
step("supports log-mode json ready output")
val (out, err, code) = _run_cli(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"cli\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports log-mode json version output

- supports log-mode json version output
- supports log-mode json version output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json version output")
step("supports log-mode json version output")
val (out, err, code) = _run_cli(["--log-mode=json", "--version"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"cli\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain("\"version\":\"")
```

</details>

#### supports dot progress for help output

- supports dot progress for help output
- supports dot progress for help output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress for help output")
step("supports dot progress for help output")
val (out, err, code) = _run_cli(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple Language")
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
val (out, err, code) = _run_cli(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### preserves check presentation options through delegation

- preserves check presentation options through delegation
- preserves check presentation options through delegation
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves check presentation options through delegation")
step("preserves check presentation options through delegation")
val (out, err, code) = _run_cli_with_echo_delegate(["check", "--json", "--progress=count", "a.spl", "b.spl"])
expect(code).to_equal(0)
expect(out).to_contain("check a.spl b.spl --json --progress=count")
```

</details>

#### rejects split check surface before delegation

- rejects split check surface before delegation
- rejects split check surface before delegation
   - Expected: code equals `1`
   - Expected: out does not contain `check a.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects split check surface before delegation")
step("rejects split check surface before delegation")
val (out, err, code) = _run_cli_with_echo_delegate(["check", "--surface", "tui", "a.spl"])
expect(code).to_equal(1)
expect(out).to_contain("invalid --surface")
expect(out.contains("check a.spl")).to_equal(false)
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
- `REQ-CLILOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1fadb5689ff152cb65cfd99ac81341c16e2bfbc19b76bc1c2fc4949dae531422`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1fadb5689ff152cb65cfd99ac81341c16e2bfbc19b76bc1c2fc4949dae531422`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1fadb5689ff152cb65cfd99ac81341c16e2bfbc19b76bc1c2fc4949dae531422`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/cli_log_modes_spec.spl
mirror: doc/06_spec/02_integration/app/cli_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/cli_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/cli_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/cli_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/cli_log_modes_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/cli_log_modes_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json ready output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/cli_log_modes_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json version output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
