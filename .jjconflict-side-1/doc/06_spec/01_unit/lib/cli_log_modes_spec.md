# Cli Log Modes Specification

> Tests covering CLI Log Modes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Log Modes Specification

## Scenarios

### CLI Log Modes

#### uses human stdout summary defaults

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses human stdout summary defaults
   - Expected: opts.valid is true
   - Expected: opts.log_mode equals `human`
   - Expected: opts.surface equals `stdout`
   - Expected: opts.progress equals `summary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses human stdout summary defaults")
val opts = parse_log_options([])
expect(opts.valid).to_equal(true)
expect(opts.log_mode).to_equal("human")
expect(opts.surface).to_equal("stdout")
expect(opts.progress).to_equal("summary")
```

</details>

#### parses LLM TUI count options

- parses LLM TUI count options
   - Expected: opts.valid is true
   - Expected: opts.log_mode equals `llm`
   - Expected: opts.surface equals `tui`
   - Expected: opts.progress equals `count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses LLM TUI count options")
val opts = parse_log_options(["--log-mode=llm", "--tui", "--progress=count"])
expect(opts.valid).to_equal(true)
expect(opts.log_mode).to_equal("llm")
expect(opts.surface).to_equal("tui")
expect(opts.progress).to_equal("count")
```

</details>

#### parses shorthand JSON and dot progress

- parses shorthand JSON and dot progress
   - Expected: opts.valid is true
   - Expected: opts.log_mode equals `json`
   - Expected: opts.progress equals `dot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses shorthand JSON and dot progress")
val opts = parse_log_options(["--json", "--dots"])
expect(opts.valid).to_equal(true)
expect(opts.log_mode).to_equal("json")
expect(opts.progress).to_equal("dot")
```

</details>

#### quiet disables progress

- quiet disables progress
   - Expected: opts.quiet is true
   - Expected: opts.progress equals `dot`
   - Expected: quiet_last.progress equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quiet disables progress")
val opts = parse_log_options(["--quiet", "--progress=dot"])
expect(opts.quiet).to_equal(true)
expect(opts.progress).to_equal("dot")
val quiet_last = parse_log_options(["--progress=dot", "--quiet"])
expect(quiet_last.progress).to_equal("none")
```

</details>

#### rejects invalid modes

- rejects invalid modes
   - Expected: opts.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid modes")
val opts = parse_log_options(["--log-mode=noisy"])
expect(opts.valid).to_equal(false)
expect(opts.error).to_contain("invalid --log-mode")
```

</details>

#### publishes help text

- publishes help text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes help text")
val lines = log_options_help()
expect(lines.len()).to_be_greater_than(0)
expect(lines[0]).to_contain("--log-mode")
```

</details>

#### renders progress modes

- renders progress modes
   - Expected: render_progress("none", 3, 10, "build") equals ``
   - Expected: render_progress("dot", 3, 10, "build") equals `.`
   - Expected: render_progress("count", 3, 10, "build") equals `3/10 build`
   - Expected: render_progress("summary", 3, 10, "build") equals `build: 3/10 (30%)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders progress modes")
expect(render_progress("none", 3, 10, "build")).to_equal("")
expect(render_progress("dot", 3, 10, "build")).to_equal(".")
expect(render_progress("count", 3, 10, "build")).to_equal("3/10 build")
expect(render_progress("summary", 3, 10, "build")).to_equal("build: 3/10 (30%)")
```

</details>

#### renders human TUI grouped counts

- renders human TUI grouped counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders human TUI grouped counts")
val groups = [
    SimpleProgressGroup.new("compile", 3, 10, "active"),
    SimpleProgressGroup.new("test", 5, 5, "done")
]
val text = render_tui_grouped_counts("build", groups)
expect(text).to_contain("build")
expect(text).to_contain("groups: 2")
expect(text).to_contain("[active] compile 3/10 (30%)")
expect(text).to_contain("[done] test 5/5 (100%)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cli_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI Log Modes.
- CLI Log Modes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d543579475963fb345a03e11a1708054cdd1d5e7c7a88252926a4a24c058b9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d543579475963fb345a03e11a1708054cdd1d5e7c7a88252926a4a24c058b9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d543579475963fb345a03e11a1708054cdd1d5e7c7a88252926a4a24c058b9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/cli_log_modes_spec.spl
mirror: doc/06_spec/01_unit/lib/cli_log_modes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/cli_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/cli_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/cli_log_modes_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses human stdout summary defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_log_modes_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses LLM TUI count options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_log_modes_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses shorthand JSON and dot progress' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
