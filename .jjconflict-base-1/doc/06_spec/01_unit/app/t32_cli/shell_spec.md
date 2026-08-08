# Shell Specification

> <details>

<!-- sdn-diagram:id=shell_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Specification

## Scenarios

### T32 Shell

#### parses simple command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = parse_shell_cmd("windows")
expect(parts.len()).to_equal(1)
expect(parts[0]).to_equal("windows")
```

</details>

#### parses command with argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = parse_shell_cmd("show break_list")
expect(parts.len()).to_equal(2)
expect(parts[0]).to_equal("show")
expect(parts[1]).to_equal("break_list")
```

</details>

#### parses set command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = parse_shell_cmd("set symbol main")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("set")
expect(parts[1]).to_equal("symbol")
expect(parts[2]).to_equal("main")
```

</details>

#### parses use command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = parse_shell_cmd("use amp0")
expect(parts[0]).to_equal("use")
expect(parts[1]).to_equal("amp0")
```

</details>

#### parses core command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = parse_shell_cmd("core a53_2")
expect(parts[0]).to_equal("core")
expect(parts[1]).to_equal("a53_2")
```

</details>

#### formats prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = "amp0"
val core = "a53_2"
val prompt = "{session}:{core}> "
expect(prompt).to_equal("amp0:a53_2> ")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/shell_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Shell

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
