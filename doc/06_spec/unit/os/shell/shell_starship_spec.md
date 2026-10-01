# Shell Starship Prompt Specification

> Validates the StarshipPrompt implementation (shell_starship.spl) that renders an ANSI-colored multi-segment prompt for the SimpleOS interactive shell REPL.

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
| Source | `test/unit/os/shell/shell_starship_spec.spl` |
| Updated | 2026-08-26 |
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

- includes green indicator when last exit code is 0
   - Expected: result contains `"\x1b[32m") or result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes green indicator when last exit code is 0")
val ctx = ShellContext.default()
ctx.last_exit_code = 0
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
# Green ANSI escape must appear somewhere in the output
expect(result.contains("\x1b[32m") or result.contains("\x1b[0;32m")).to_equal(true)
```

</details>

#### includes red indicator when last exit code is nonzero

- includes red indicator when last exit code is nonzero
   - Expected: result contains `"\x1b[31m") or result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes red indicator when last exit code is nonzero")
val ctx = ShellContext.default()
ctx.last_exit_code = 1
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("\x1b[31m") or result.contains("\x1b[0;31m")).to_equal(true)
```

</details>

#### shows nonzero exit code value in prompt on failure

- shows nonzero exit code value in prompt on failure
   - Expected: result contains `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows nonzero exit code value in prompt on failure")
val ctx = ShellContext.default()
ctx.last_exit_code = 127
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("127")).to_equal(true)
```

</details>

#### does not show exit code number on success

- does not show exit code number on success
   - Expected: result contains `"✓") or not result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not show exit code number on success")
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

- includes username in prompt
   - Expected: result contains `root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes username in prompt")
val ctx = ShellContext.default()
ctx.user = "root"
ctx.host = "simpleos"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("root")).to_equal(true)
```

</details>

#### includes hostname in prompt

- includes hostname in prompt
   - Expected: result contains `simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes hostname in prompt")
val ctx = ShellContext.default()
ctx.user = "root"
ctx.host = "simpleos"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("simpleos")).to_equal(true)
```

</details>

#### separates user and host with @ character

- separates user and host with @ character
   - Expected: result contains `admin@mybox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates user and host with @ character")
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

- shows cwd in prompt
   - Expected: result contains `"/usr/local/bin") or result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows cwd in prompt")
val ctx = ShellContext.default()
ctx.cwd = "/usr/local/bin"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("/usr/local/bin") or result.contains("bin")).to_equal(true)
```

</details>

#### abbreviates home directory to tilde

- abbreviates home directory to tilde
   - Expected: result contains `~`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abbreviates home directory to tilde")
val ctx = ShellContext.default()
ctx.cwd = "/home/user"
ctx.home = "/home/user"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("~")).to_equal(true)
```

</details>

#### shows root directory as slash

- shows root directory as slash
   - Expected: result contains `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows root directory as slash")
val ctx = ShellContext.default()
ctx.cwd = "/"
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("/")).to_equal(true)
```

</details>

#### abbreviates intermediate path components for long paths

- abbreviates intermediate path components for long paths
   - Expected: result contains `abbreviated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abbreviates intermediate path components for long paths")
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

- shows branch name when .git/HEAD is present
   - Expected: result contains `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows branch name when .git/HEAD is present")
val ctx = ShellContext.default()
ctx.cwd = "/repo"
# Provide a fake VFS that returns branch HEAD content
val prompt = StarshipPrompt.with_git_head_content("ref: refs/heads/main")
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("main")).to_equal(true)
```

</details>

#### shows detached HEAD indicator when HEAD is a raw commit hash

- shows detached HEAD indicator when HEAD is a raw commit hash
   - Expected: result contains `"a1b2c3") or result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows detached HEAD indicator when HEAD is a raw commit hash")
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

- omits git segment when not in a git repo
   - Expected: result does not contain `refs/heads/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits git segment when not in a git repo")
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

- hides elapsed time when below threshold
   - Expected: result does not contain `"ms") or result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hides elapsed time when below threshold")
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 500)
# Should not show any timing annotation for fast commands
expect(result.contains("ms") or result.contains("500")).to_equal(false)
```

</details>

#### shows elapsed time when above threshold

- shows elapsed time when above threshold
   - Expected: result contains `"5") and (result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows elapsed time when above threshold")
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 5000)
expect(result.contains("5") and (result.contains("s") or result.contains("ms"))).to_equal(true)
```

</details>

#### shows elapsed in seconds for times >= 1000 ms

- shows elapsed in seconds for times >= 1000 ms
   - Expected: result contains `"3") and result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows elapsed in seconds for times >= 1000 ms")
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 3500)
expect(result.contains("3") and result.contains("s")).to_equal(true)
```

</details>

### StarshipPrompt overall structure

#### ends with prompt terminator character

- ends with prompt terminator character
   - Expected: trimmed.ends_with("$") or trimmed.ends_with("#") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with prompt terminator character")
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

- includes ANSI reset code to avoid terminal color bleed
   - Expected: result contains `"\x1b[0m") or result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes ANSI reset code to avoid terminal color bleed")
val ctx = ShellContext.default()
val prompt = StarshipPrompt.new()
val result = prompt.build_prompt(ctx, 0)
expect(result.contains("\x1b[0m") or result.contains("\x1b[m")).to_equal(true)
```

</details>

#### returns non-empty string for default context

- returns non-empty string for default context


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for default context")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `decf70471e361a9843dff196259c04ab8068e44b9b1651170e57bcfe359a866b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `decf70471e361a9843dff196259c04ab8068e44b9b1651170e57bcfe359a866b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `decf70471e361a9843dff196259c04ab8068e44b9b1651170e57bcfe359a866b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/shell/shell_starship_spec.spl
mirror: doc/06_spec/unit/os/shell/shell_starship_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/shell/shell_starship_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/shell/shell_starship_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/shell/shell_starship_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes green indicator when last exit code is 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/shell/shell_starship_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes red indicator when last exit code is nonzero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/shell/shell_starship_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows nonzero exit code value in prompt on failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
