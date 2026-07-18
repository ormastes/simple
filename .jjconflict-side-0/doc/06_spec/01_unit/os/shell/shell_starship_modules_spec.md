# Shell Starship Module Specification

> Complements shell_starship_spec.spl by exercising the AC-4 modules that the original spec does not cover directly: ASCII-fallback glyphs, jobs module, character module suffix, and extended cmd_duration formatting.

<!-- sdn-diagram:id=shell_starship_modules_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_starship_modules_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_starship_modules_spec -> std
shell_starship_modules_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_starship_modules_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/os/shell/shell_starship_modules_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Complements shell_starship_spec.spl by exercising the AC-4 modules that the
original spec does not cover directly: ASCII-fallback glyphs, jobs module,
character module suffix, and extended cmd_duration formatting.

## Scenarios

### StarshipPrompt jobs module
_Background job count appears only when at least one job is tracked._

#### hides jobs segment when no background jobs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.jobs_count = 0
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
# No jobs marker should appear — we use  (NF_JOBS) or "jobs:" fallback
expect(result.contains("jobs:")).to_equal(false)
```

</details>

#### shows jobs segment when 1+ background jobs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.user = "user"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.trim_end().ends_with("$")).to_equal(true)
```

</details>

#### emits # suffix for root user

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
# 2001 > 2000 threshold → show, and 2001/1000 = 2s
val result = prompt.build_prompt(ctx, 2001)
expect(result.contains("2s")).to_equal(true)
```

</details>

### StarshipPrompt render budget (AC-6)

#### completes a full build_prompt call in under 500 ms wall-clock

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
