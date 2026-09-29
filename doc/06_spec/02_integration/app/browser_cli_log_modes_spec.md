# browser_cli_log_modes_spec

> Purpose: This spec proves Simple Browser CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_cli_log_modes_spec

Purpose: This spec proves Simple Browser CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/browser_cli_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Simple Browser CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Simple Browser CLI options

#### shows shared log options and the --open flag in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared log options and the --open flag in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BROWSERCLILOGMODES-001
step("shows shared log options and the --open flag in help")
val (out, err, code) = _run_browser(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Browser")
expect(out).to_contain("--open")
expect(out).to_contain("--log-mode")
```

</details>

#### supports --version

- supports --version
- supports --version
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports --version")
step("supports --version")
val (out, err, code) = _run_browser(["--version"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Browser")
```

</details>

#### rejects an unknown option before reaching the render engine

- rejects an unknown option before reaching the render engine
- rejects an unknown option before reaching the render engine
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an unknown option before reaching the render engine")
step("rejects an unknown option before reaching the render engine")
val (out, err, code) = _run_browser(["--log-mode=json", "--bogus"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown browser option: --bogus")
```

</details>

#### does not reject --open as an unknown option

- does not reject --open as an unknown option
- does not reject --open as an unknown option
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not reject --open as an unknown option")
step("does not reject --open as an unknown option")
# --open is checked by the SAME browser_first_unknown_option()
# allowlist as the case above, so this is fast (it returns from
# that check before main.spl ever calls run_browser_window_gui /
# the render engine) -- it just confirms --open didn't regress
# into the "unknown option" branch, without actually launching.
val (out, err, code) = _run_browser(["--log-mode=json", "--open", "--bogus"])
expect(code).to_equal(1)
expect(out).to_contain("Unknown browser option: --bogus")
expect(out).to_not_contain("Unknown browser option: --open")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-BROWSERCLILOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fbeeea4a557c209f0f7a7de22cb18e980e192d2f57ebe72791c158b7b241e107`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fbeeea4a557c209f0f7a7de22cb18e980e192d2f57ebe72791c158b7b241e107`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fbeeea4a557c209f0f7a7de22cb18e980e192d2f57ebe72791c158b7b241e107`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/browser_cli_log_modes_spec.spl
mirror: doc/06_spec/02_integration/app/browser_cli_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/browser_cli_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/browser_cli_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/browser_cli_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/browser_cli_log_modes_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options and the --open flag in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/browser_cli_log_modes_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports --version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/browser_cli_log_modes_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown option before reaching the render engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
