# Shell Starship Module Specification

> Complements shell_starship_spec.spl by exercising the AC-4 modules that the original spec does not cover directly: ASCII-fallback glyphs, jobs module, character module suffix, and extended cmd_duration formatting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Starship Module Specification

Complements shell_starship_spec.spl by exercising the AC-4 modules that the original spec does not cover directly: ASCII-fallback glyphs, jobs module, character module suffix, and extended cmd_duration formatting.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #shell-starship-modules |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/unit/os/shell/shell_starship_modules_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Complements shell_starship_spec.spl by exercising the AC-4 modules that the
original spec does not cover directly: ASCII-fallback glyphs, jobs module,
character module suffix, and extended cmd_duration formatting.

## Scenarios

### StarshipPrompt jobs module

#### hides jobs segment when no background jobs

- hides jobs segment when no background jobs
   - Expected: result does not contain `jobs:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hides jobs segment when no background jobs")
val ctx = ShellContext.default()
ctx.jobs_count = 0
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
# No jobs marker should appear — we use  (NF_JOBS) or "jobs:" fallback
expect(result.contains("jobs:")).to_equal(false)
```

</details>

#### shows jobs segment when 1+ background jobs

- shows jobs segment when 1+ background jobs
   - Expected: result contains `"jobs: 3") or result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows jobs segment when 1+ background jobs")
val ctx = ShellContext.default()
ctx.jobs_count = 3
val prompt = StarshipPrompt.new()
prompt.use_nerd_font = false
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("jobs: 3") or result.contains("jobs:3")).to_equal(true)
```

</details>

### StarshipPrompt character module
_Character module emits $ for non-root, # for root, always present._

#### emits $ suffix for non-root user

- emits $ suffix for non-root user
   - Expected: result.trim_end().ends_with("$") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits $ suffix for non-root user")
val ctx = ShellContext.default()
ctx.user = "user"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.trim_end().ends_with("$")).to_equal(true)
```

</details>

#### emits # suffix for root user

- emits # suffix for root user
   - Expected: result.trim_end().ends_with("#") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits # suffix for root user")
val ctx = ShellContext.default()
ctx.user = "root"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.trim_end().ends_with("#")).to_equal(true)
```

</details>

### StarshipPrompt ASCII fallback
_When use_nerd_font is disabled, ASCII replacements must appear._

#### uses ASCII ok glyph when nerd fonts disabled and exit is 0

- uses ASCII ok glyph when nerd fonts disabled and exit is 0
   - Expected: result contains `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses ASCII ok glyph when nerd fonts disabled and exit is 0")
val ctx = ShellContext.default()
ctx.last_exit_code = 0
val prompt = StarshipPrompt.new()
prompt.use_nerd_font = false
val result = prompt.build_prompt(ctx, 0)
# ASCII_OK = "v"; the success glyph should render as "v"
expect(result.contains("v")).to_equal(true)
```

</details>

#### uses ASCII fail glyph when nerd fonts disabled and exit is non-zero

- uses ASCII fail glyph when nerd fonts disabled and exit is non-zero
   - Expected: result contains `x(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses ASCII fail glyph when nerd fonts disabled and exit is non-zero")
val ctx = ShellContext.default()
ctx.last_exit_code = 2
val prompt = StarshipPrompt.new()
prompt.use_nerd_font = false
val result = prompt.build_prompt(ctx, 0)
# ASCII_FAIL = "x"; exit code 2 rendered as "x(2)"
expect(result.contains("x(2)")).to_equal(true)
```

</details>

### StarshipPrompt module toggles
_AC-4 requires modules to be individually toggleable._

#### disabling show_status removes exit indicator

- disabling show_status removes exit indicator
   - Expected: result does not contain `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disabling show_status removes exit indicator")
val ctx = ShellContext.default()
ctx.last_exit_code = 127
val prompt = StarshipPrompt.new()
prompt.show_status = false
val result = prompt.build_prompt(ctx, 0)
# With status disabled, "127" must not leak from the exit module
expect(result.contains("127")).to_equal(false)
```

</details>

#### disabling show_directory removes cwd segment

- disabling show_directory removes cwd segment
   - Expected: result does not contain `project`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disabling show_directory removes cwd segment")
val ctx = ShellContext.default()
ctx.cwd = "/tmp/workspace/project"
val prompt = StarshipPrompt.new()
prompt.show_directory = false
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("project")).to_equal(false)
```

</details>

### StarshipPrompt cmd_duration formatting
_Extended cmd_duration: ms for sub-second, s for >= 1s._

#### formats just-above-threshold duration in seconds

- formats just-above-threshold duration in seconds
   - Expected: result contains `2s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats just-above-threshold duration in seconds")
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
# 2001 > 2000 threshold → show, and 2001/1000 = 2s
val result = prompt.build_prompt(ctx, 2001)
expect(result.contains("2s")).to_equal(true)
```

</details>

### StarshipPrompt render budget (AC-6)

#### completes a full build_prompt call in under 500 ms wall-clock

- completes a full build_prompt call in under 500 ms wall-clock


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes a full build_prompt call in under 500 ms wall-clock")
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val t0 = current_time_ms()
val result = prompt.build_prompt(ctx, 0)
val elapsed = current_time_ms() - t0
# Assert the prompt produced output (sanity) and finished in time
expect(result.len()).to_be_greater_than(0)
expect(elapsed).to_be_less_than(500)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `ea5cf2be980fbfc9bba9e5ba8ba29c36949bd98dc64682f37bc3f1dbefea0594`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea5cf2be980fbfc9bba9e5ba8ba29c36949bd98dc64682f37bc3f1dbefea0594`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea5cf2be980fbfc9bba9e5ba8ba29c36949bd98dc64682f37bc3f1dbefea0594`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/shell/shell_starship_modules_spec.spl
mirror: doc/06_spec/unit/os/shell/shell_starship_modules_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/shell/shell_starship_modules_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/shell/shell_starship_modules_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/shell/shell_starship_modules_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hides jobs segment when no background jobs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/shell/shell_starship_modules_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows jobs segment when 1+ background jobs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/shell/shell_starship_modules_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits $ suffix for non-root user' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
