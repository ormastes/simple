# Cli Args Mutability Specification

> Tests covering compiler driver CLI args mutability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Args Mutability Specification

## Scenarios

### compiler driver CLI args mutability

#### marks mutating legacy opt-level helper as me

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- marks mutating legacy opt-level helper as me
   - Expected: source does not contain `fn apply_legacy_opt_level(level: i64):`
   - Expected: source does not contain `val arg = if val next_arg = self.next()`
   - Expected: source does not contain `val file = if val next_file = self.next()`
   - Expected: source does not contain `= if val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks mutating legacy opt-level helper as me")
val source = file_read("src/compiler/80.driver/main.spl")

expect(source).to_contain("me apply_legacy_opt_level(level: i64):")
expect(source).to_contain("me parse_long_option(arg: text, mut result: CliArgs)")
expect(source).to_contain("fn apply_option(name: text, value: text, mut result: CliArgs)")
expect(source).to_contain("me parse_short_option(arg: text, mut result: CliArgs)")
expect(source.contains("fn apply_legacy_opt_level(level: i64):")).to_equal(false)
expect(source.contains("val arg = if val next_arg = self.next()")).to_equal(false)
expect(source.contains("val file = if val next_file = self.next()")).to_equal(false)
expect(source.contains("= if val")).to_equal(false)
```

</details>

#### transports standalone mode as text past aggregate copies

- transports standalone mode as text past aggregate copies
   - Expected: main_source does not contain `options.build_mode =`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("transports standalone mode as text past aggregate copies")
val main_source = file_read("src/compiler/80.driver/main.spl")
# Repointed 2026-08-21: compile-mode dispatch moved to
# driver_orchestration.spl in the driver.spl split (4b88aebf00b).
val driver_source = file_read("src/compiler/80.driver/driver_orchestration.spl")
val types_source = file_read("src/compiler/80.driver/driver_types.spl")
val options_source = file_read("src/compiler/00.common/driver_core_types.spl")

expect(main_source).to_contain("options.cli_mode_text = requested_mode_text")
expect(main_source.contains("options.build_mode =")).to_equal(false)
expect(options_source).to_contain("    cli_mode_text: text\n")
expect(options_source).to_not_contain("cli_mode_text: text =")
expect(options_source).to_contain("cli_mode_text: opts.cli_mode_text")
expect(main_source).to_contain("elif arg == \"-m\" or arg == \"--mode\":")
expect(main_source).to_contain("Error: Unknown mode:")
expect(main_source).to_contain("requested_mode_text = _canonical_compile_mode_text(text)")
expect(types_source).to_contain("val backend = if selected_mode_text == \"interpret\"")
expect(driver_source).to_contain("compile_mode_text = self.ctx.options.cli_mode_text")
expect(driver_source).to_contain("if compile_mode_text == \"aot\":")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/cli_args_mutability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compiler driver CLI args mutability.
- compiler driver CLI args mutability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1cabeded9b3945a19f2dbcd4dcb5eede9694d24b2001d587573ad97a8617d3f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1cabeded9b3945a19f2dbcd4dcb5eede9694d24b2001d587573ad97a8617d3f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1cabeded9b3945a19f2dbcd4dcb5eede9694d24b2001d587573ad97a8617d3f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/cli_args_mutability_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/cli_args_mutability_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/cli_args_mutability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/cli_args_mutability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/cli_args_mutability_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/cli_args_mutability_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks mutating legacy opt-level helper as me' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/cli_args_mutability_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transports standalone mode as text past aggregate copies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
