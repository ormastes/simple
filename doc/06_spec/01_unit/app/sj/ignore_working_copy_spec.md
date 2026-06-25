# Ignore Working Copy Specification

> <details>

<!-- sdn-diagram:id=ignore_working_copy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ignore_working_copy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ignore_working_copy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ignore_working_copy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ignore Working Copy Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/ignore_working_copy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Ignore Working Copy - Read Verbs

#### injects --ignore-working-copy for jj log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "log"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "status"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "diff"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj show

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "show"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj op log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "op", "log"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj evolog

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "evolog"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj file annotate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "file", "annotate", "src/main.spl"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj file list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "file", "list"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj file show

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "file", "show", "path"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj bookmark list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "bookmark", "list"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj config list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "config", "list"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj op show

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "op", "show"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

### Ignore Working Copy - No-Pager and Color

#### all commands get --no-pager

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "describe", "-m", "test"])
expect(_has_flag(result, "--no-pager")).to_equal(true)
```

</details>

#### all commands get --color never

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "describe", "-m", "test"])
expect(_has_flag(result, "--color")).to_equal(true)
expect(_has_flag(result, "never")).to_equal(true)
```

</details>

### Ignore Working Copy - Negative Cases

#### does NOT inject --ignore-working-copy for jj describe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "describe", "-m", "test"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(false)
```

</details>

#### does NOT inject --ignore-working-copy for jj new

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "new"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(false)
```

</details>

#### does NOT inject --ignore-working-copy for jj rebase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["jj", "rebase", "-d", "main"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(false)
```

</details>

#### does not modify non-jj commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = inject_flags(["git", "status"])
expect(result.len()).to_equal(2i64)
expect(result[0i64]).to_equal("git")
```

</details>

#### build_command combines inject and join

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_command(["jj", "log"])
expect(cmd).to_contain("--ignore-working-copy")
expect(cmd).to_contain("--no-pager")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
