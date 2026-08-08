# Shell Starship Prompt Specification

> Validates the StarshipPrompt implementation (shell_starship.spl) that renders an ANSI-colored multi-segment prompt for the SimpleOS interactive shell REPL.

<!-- sdn-diagram:id=shell_starship_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_starship_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_starship_spec -> std
shell_starship_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_starship_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Starship Prompt Specification

Validates the StarshipPrompt implementation (shell_starship.spl) that renders an ANSI-colored multi-segment prompt for the SimpleOS interactive shell REPL.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #shell-starship-prompt |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/shell/shell_starship_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the StarshipPrompt implementation (shell_starship.spl) that renders
an ANSI-colored multi-segment prompt for the SimpleOS interactive shell REPL.

Segments covered:
- Exit-code indicator (green check / red cross with exit code)
- user@host segment
- Current working directory (cwd) with path abbreviation
- Git branch segment (reads .git/HEAD from VFS)
- Elapsed time indicator (shown when > threshold ms)

Configuration is read from ~/.config/starship.spl when present.

## Key Concepts

| Concept | Description |
|---------|-------------|
| StarshipPrompt | Struct that builds the full prompt string via build_prompt(ctx, elapsed_ms) |
| ShellContext | Provides cwd, last_exit_code, vfs reference, user/host info |
| ANSI codes | e.g. \\e[32m = green, \\e[31m = red, \\e[0m = reset |
| Git segment | Reads VFS path <cwd>/.git/HEAD to detect branch name |
| Elapsed segment | Shown when elapsed_ms > StarshipPrompt.elapsed_threshold_ms |

## Scenarios

### StarshipPrompt exit-code segment

#### includes green indicator when last exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.last_exit_code = 0
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
# Green ANSI escape must appear somewhere in the output
expect(result.contains("\x1b[32m") or result.contains("\x1b[0;32m")).to_equal(true)
```

</details>

#### includes red indicator when last exit code is nonzero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.last_exit_code = 1
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("\x1b[31m") or result.contains("\x1b[0;31m")).to_equal(true)
```

</details>

#### shows nonzero exit code value in prompt on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.last_exit_code = 127
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("127")).to_equal(true)
```

</details>

#### does not show exit code number on success

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.last_exit_code = 0
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
# "0" should not appear as exit-code in the prompt (zero is implicit)
expect(result.contains("✓") or not result.contains(" 0 ")).to_equal(true)
```

</details>

### StarshipPrompt user@host segment

#### includes username in prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.user = "root"
ctx.host = "simpleos"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("root")).to_equal(true)
```

</details>

#### includes hostname in prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.user = "root"
ctx.host = "simpleos"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("simpleos")).to_equal(true)
```

</details>

#### separates user and host with @ character

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.user = "admin"
ctx.host = "mybox"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("admin@mybox")).to_equal(true)
```

</details>

### StarshipPrompt cwd segment

#### shows cwd in prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.cwd = "/usr/local/bin"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("/usr/local/bin") or result.contains("bin")).to_equal(true)
```

</details>

#### abbreviates home directory to tilde

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.cwd = "/home/user"
ctx.home = "/home/user"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("~")).to_equal(true)
```

</details>

#### shows root directory as slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.cwd = "/"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("/")).to_equal(true)
```

</details>

#### abbreviates intermediate path components for long paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.cwd = "/very/long/nested/path/that/should/be/abbreviated"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
# Result must include the leaf component
expect(result.contains("abbreviated")).to_equal(true)
```

</details>

### StarshipPrompt git branch segment

#### shows branch name when .git/HEAD is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.cwd = "/repo"
# Provide a fake VFS that returns branch HEAD content
val prompt = StarshipPrompt.with_git_head_content("ref: refs/heads/main")
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("main")).to_equal(true)
```

</details>

#### shows detached HEAD indicator when HEAD is a raw commit hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.cwd = "/repo"
val hash = "a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2"
val prompt = StarshipPrompt.with_git_head_content(hash)
val result = prompt.build_prompt(ctx, 0)
# At minimum the truncated hash or a detached indicator must appear
expect(result.contains("a1b2c3") or result.contains("HEAD")).to_equal(true)
```

</details>

#### omits git segment when not in a git repo

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.cwd = "/tmp"
val prompt = StarshipPrompt.with_no_git()
val result = prompt.build_prompt(ctx, 0)
# Branch-specific Unicode or "branch" text must be absent
expect(result.contains("refs/heads/")).to_equal(false)
```

</details>

### StarshipPrompt elapsed time segment

#### hides elapsed time when below threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 500)
# Should not show any timing annotation for fast commands
expect(result.contains("ms") or result.contains("500")).to_equal(false)
```

</details>

#### shows elapsed time when above threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 5000)
expect(result.contains("5") and (result.contains("s") or result.contains("ms"))).to_equal(true)
```

</details>

#### shows elapsed in seconds for times >= 1000 ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 3500)
expect(result.contains("3") and result.contains("s")).to_equal(true)
```

</details>

### StarshipPrompt overall structure

#### ends with prompt terminator character

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.user = "user"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
# Prompt must end with $ or # (possibly after reset code)
val trimmed = result.trim_end()
expect(trimmed.ends_with("$") or trimmed.ends_with("#")).to_equal(true)
```

</details>

#### includes ANSI reset code to avoid terminal color bleed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("\x1b[0m") or result.contains("\x1b[m")).to_equal(true)
```

</details>

#### returns non-empty string for default context

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
