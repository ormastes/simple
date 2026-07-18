# Sed Specification

> <details>

<!-- sdn-diagram:id=sed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sed_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sed Specification

## Scenarios

### sed tool

#### substitute parsing

#### parses basic substitute command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_substitute("s/hello/world/")
expect(cmd.cmd_type).to_equal("s")
expect(cmd.pattern).to_equal("hello")
expect(cmd.replacement).to_equal("world")
expect(cmd.global_flag).to_equal(false)
```

</details>

#### parses global substitute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_substitute("s/a/b/g")
expect(cmd.cmd_type).to_equal("s")
expect(cmd.global_flag).to_equal(true)
```

</details>

#### parses empty replacement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_substitute("s/foo//")
expect(cmd.cmd_type).to_equal("s")
expect(cmd.pattern).to_equal("foo")
expect(cmd.replacement).to_equal("")
```

</details>

#### script parsing

#### parses delete command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_sed_script("d")
expect(cmd.cmd_type).to_equal("d")
```

</details>

#### parses print command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_sed_script("p")
expect(cmd.cmd_type).to_equal("p")
```

</details>

#### parses quit command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_sed_script("q")
expect(cmd.cmd_type).to_equal("q")
```

</details>

#### command application

#### applies substitute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_substitute("s/hello/world/")
val result = apply_command("hello there", cmd)
expect(result.0).to_equal("world there")
expect(result.1).to_equal(true)
```

</details>

#### applies delete

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = parse_sed_script("d")
val result = apply_command("line", cmd)
expect(result.1).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/sed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sed tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
